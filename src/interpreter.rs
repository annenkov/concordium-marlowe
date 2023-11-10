//! Syntax and interpreter for a subset of Marlowe.
//! Follows https://github.com/input-output-hk/marlowe/tree/master/haskell/src/Language/Marlowe

use core::{
    cmp::min,
    fmt::Debug,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

use concordium_std::{collections::BTreeMap, *};

type Timeout = Timestamp;

struct TimeInterval {
    from: Timestamp,
    to: Timestamp,
}

struct Enviroment {
    time_interval: TimeInterval,
}

/// Additive identity
trait Zero {
    fn zero() -> Self;
}

trait Money:
    Sized
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + MulAssign
    + Div<Output = Self>
    + DivAssign
    + PartialOrd
    + Ord
    + PartialEq
    + Zero
    + Copy
    + Debug
    + Clone
    + Copy
{
}

#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Clone)]
enum Party {
    Role(String),
}

#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Clone)]
enum Payee {
    Party(Party),
}

#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Clone)]
struct Token {
    id: String,
    name: String,
}

#[derive(Debug)]
enum Value<M: Money> {
    Constant(M),
    Add(Box<Value<M>>, Box<Value<M>>),
    Sub(Box<Value<M>>, Box<Value<M>>),
    Mul(Box<Value<M>>, Box<Value<M>>),
    Div(Box<Value<M>>, Box<Value<M>>),
}

impl<M: Money> Value<M> {
    fn eval(&self) -> M {
        match self {
            Value::Constant(i) => *i,
            Value::Add(lhs, rhs) => lhs.eval() + rhs.eval(),
            Value::Sub(lhs, rhs) => lhs.eval() - rhs.eval(),
            Value::Mul(lhs, rhs) => lhs.eval() * rhs.eval(),
            Value::Div(lhs, rhs) => lhs.eval() / rhs.eval(),
        }
    }
}

#[derive(Debug)]
enum Action<M: Money> {
    Deposit(Party, Party, Token, Value<M>),
}

#[derive(Debug)]
struct Case<M: Money> {
    action: Action<M>,
    contract: Contract<M>,
}

#[derive(Debug)]
enum Contract<M: Money> {
    Pay(Party, Payee, Token, Value<M>, Box<Contract<M>>),
    When(Vec<Case<M>>, Timeout, Box<Contract<M>>),
    Close,
}

type Accounts<M: Money> = BTreeMap<(Party, Token), M>;

#[derive(Debug)]
struct State<M> {
    min_time: Timestamp,
    accounts: Accounts<M>,
}

impl<M: Money> State<M> {
    fn add_money(&mut self, party: Party, token: Token, amount: M) {
        let entry = self
            .accounts
            .entry((party, token))
            .or_insert_with(|| M::zero());
        *entry += amount
    }
}

#[derive(Debug, Clone)]
struct Payment<M: Money> {
    party: Party,
    payee: Payee,
    token: Token,
    money: M,
}

enum ReduceEffect<M: Money> {
    ReduceWithPayment(Payment<M>),
    ReduceNoPayment,
}

// TODO: add other types of warnings
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum ReduceWarning {
    NoWarning,
}

struct ReducedData<M: Money> {
    warning: ReduceWarning,
    effect: ReduceEffect<M>,
    contract: Contract<M>,
}

enum ReducedSuccess<M: Money> {
    Reduced(ReduceWarning, ReduceEffect<M>, Box<Contract<M>>),
    NotReduced(Box<Contract<M>>),
}

enum ReduceStepError {
    AmbiguousTimeIntervalReductionError,
}

enum ReduceStepResult<M: Money> {
    Reduced(ReducedData<M>),
    NotReduced,
    AmbiguousTimeIntervalReductionError,
}

/// Pick the first account with money in it
fn refund_one<M: Money>(accounts: &mut Accounts<M>) -> Option<(Party, Token, M)> {
    while let Some(((party, token), balance)) = accounts.pop_first() {
        if balance > M::zero() {
            return Some((party, token, balance));
        }
    }
    None
}

impl<M: Money> Contract<M> {
    fn reduce_step(
        self,
        env: &Enviroment,
        state: &mut State<M>,
    ) -> Result<ReducedSuccess<M>, ReduceStepError> {
        match self {
            Contract::Pay(party, payee, token, value, residual_contract) => {
                let money_to_pay = value.eval();
                let balance = state
                    .accounts
                    .get(&(party.clone(), token.clone()))
                    .map(|x| *x)
                    .unwrap_or(M::zero());
                // NOTE: the contract payoff is limited by the corresponding account balance ("account" in the internal sense - a balance stored by the manager contract);
                // this seems a bit odd, I would expect the contract evaluation to fail/get stuck.
                // The original semantics is a bit more complex: it covers the case of paying to and internal account of a manager contract. We ignore this case here.
                let paid_money = min(balance, money_to_pay);
                Ok(ReducedSuccess::Reduced(
                    ReduceWarning::NoWarning,
                    ReduceEffect::ReduceWithPayment(Payment {
                        party: party.clone(),
                        payee: payee.clone(),
                        token: token.clone(),
                        money: paid_money,
                    }),
                    residual_contract,
                ))
            }
            Contract::When(case, timeout, residual_contract) => {
                let start_time = env.time_interval.from;
                let end_time = env.time_interval.to;
                // if timeout in future – do not reduce
                if end_time < timeout {
                    Ok(ReducedSuccess::NotReduced(Box::new(Contract::When(
                        case,
                        timeout,
                        residual_contract,
                    ))))
                }
                // if timeout in the past – reduce to timeout continuation
                else if timeout <= start_time {
                    Ok(ReducedSuccess::Reduced(
                        ReduceWarning::NoWarning,
                        ReduceEffect::ReduceNoPayment,
                        residual_contract,
                    ))
                }
                // if timeout in the time range – issue an ambiguity error
                else {
                    Err(ReduceStepError::AmbiguousTimeIntervalReductionError)
                }
            }
            Contract::Close => match refund_one(&mut state.accounts) {
                Some((party, token, balance)) => Ok(ReducedSuccess::Reduced(
                    ReduceWarning::NoWarning,
                    ReduceEffect::ReduceWithPayment(Payment {
                        party: party.clone(),
                        payee: Payee::Party(party),
                        token: token,
                        money: balance,
                    }),
                    Box::new(Contract::Close),
                )),
                None => Ok(ReducedSuccess::NotReduced(Box::new(self))),
            },
        }
    }
}

/// Carry a step of the contract with no inputs
fn reduce_contract_step<M: Money>(
    env: &Enviroment,
    state: &mut State<M>,
    contract: Contract<M>,
) -> ReduceStepResult<M> {
    match contract {
        Contract::Pay(party, payee, token, value, residual_contract) => {
            let money_to_pay = value.eval();
            let balance = state
                .accounts
                .get(&(party.clone(), token.clone()))
                .map(|x| *x)
                .unwrap_or(M::zero());
            // NOTE: the contract payoff is limited by the corresponding account balance ("account" in the internal sense - a balance stored by the manager contract);
            // this seems a bit odd, I would expect the contract evaluation to fail/get stuck.
            // The original semantics is a bit more complex: it covers the case of paying to and internal account of a manager contract. We ignore this case here.
            let paid_money = min(balance, money_to_pay);
            ReduceStepResult::Reduced(ReducedData {
                warning: ReduceWarning::NoWarning,
                effect: ReduceEffect::ReduceWithPayment(Payment {
                    party: party,
                    payee: payee,
                    token: token,
                    money: paid_money,
                }),
                contract: *residual_contract,
            })
        }
        Contract::When(_, timeout, residual_contract) => {
            let start_time = env.time_interval.from;
            let end_time = env.time_interval.to;
            // if timeout in future – do not reduce
            if end_time < timeout {
                ReduceStepResult::NotReduced
            }
            // if timeout in the past – reduce to timeout continuation
            else if timeout <= start_time {
                ReduceStepResult::Reduced(ReducedData {
                    warning: ReduceWarning::NoWarning,
                    effect: ReduceEffect::ReduceNoPayment,
                    contract: *residual_contract,
                })
            }
            // if timeout in the time range – issue an ambiguity error
            else {
                ReduceStepResult::AmbiguousTimeIntervalReductionError
            }
        }
        Contract::Close => match refund_one(&mut state.accounts) {
            Some((party, token, balance)) => ReduceStepResult::Reduced(ReducedData {
                warning: ReduceWarning::NoWarning,
                effect: ReduceEffect::ReduceWithPayment(Payment {
                    party: party.clone(),
                    payee: Payee::Party(party),
                    token: token,
                    money: balance,
                }),
                contract: Contract::Close,
            }),
            None => ReduceStepResult::NotReduced,
        },
    }
}

struct ContractQuiescent<M: Money> {
    is_reduced: bool,
    warnings: Vec<ReduceWarning>,
    payments: Vec<Payment<M>>,
    contract: Box<Contract<M>>,
}

enum ReduceError {
    AmbiguousTimeIntervalError,
}

impl From<ReduceStepError> for ReduceError {
    fn from(_: ReduceStepError) -> Self {
        ReduceError::AmbiguousTimeIntervalError
    }
}

type ReduceResult<M: Money> = Result<ContractQuiescent<M>, ReduceError>;

/// Reduce a contract until it cannot be reduced more
// reduceContractUntilQuiescent :: Environment -> State -> Contract -> ReduceResult
fn reduce_contract_until_quiescent<M: Money>(
    env: &Enviroment,
    state: &mut State<M>,
    contract: Box<Contract<M>>,
) -> ReduceResult<M> {
    let mut warnings = Vec::new();
    let mut payments = Vec::new();
    let mut residual_contract = contract;
    let mut is_reduced = false;

    let res = loop {
        let reduce_success = residual_contract.reduce_step(env, state)?;
        match reduce_success {
            ReducedSuccess::Reduced(warning, effect, contract) => {
                // Reduce, while the contract is reducible
                if warning != ReduceWarning::NoWarning {
                    warnings.push(warning)
                };
                if let ReduceEffect::ReduceWithPayment(payment) = effect {
                    payments.push(payment)
                }
                is_reduced = true;
                residual_contract = contract;
            }
            ReducedSuccess::NotReduced(contract) => {
                // if not reducible, the reduction is done.
                break ContractQuiescent {
                    is_reduced,
                    warnings,
                    payments,
                    contract: contract,
                };
            }
        }
    };
    Ok(res)
}

// TODO: add other types of warnings
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum ApplyWarning {
    ApplyNoWarning,
}

#[derive(Debug, Clone)]
enum InputContent<M: Money> {
    IDeposit(Party, Party, Token, M),
}

type ApplyAction = Option<ApplyWarning>;

/// Try to apply a single input contentent to a single action
// applyAction :: Environment -> State -> InputContent -> Action -> ApplyAction
//applyAction env state (IDeposit accId1 party1 token1 money) (Deposit accId2 party2 token2 val) =
fn apply_action<M: Money>(
    _env: &Enviroment,
    state: &mut State<M>,
    input: &InputContent<M>,
    action: &Action<M>,
) -> ApplyAction {
    match (input, action) {
        (
            InputContent::IDeposit(party_in1, party_in2, token1, amount1),
            Action::Deposit(party1, party2, token2, value),
        ) => {
            let amount2 = value.eval();
            // TODO: What is party2 role in all this?
            if *party_in1 == *party1
                && *party_in2 == *party2
                && *token1 == *token2
                && *amount1 == amount2
            {
                state.add_money(party_in1.clone(), token1.clone(), *amount1);
            }
            Some(ApplyWarning::ApplyNoWarning)
        }
    }
}

type ApplyResult<M: Money> = Option<(ApplyWarning, Contract<M>)>;

/// Apply a single input to the contract (assumes the contract is reduced)
fn apply_cases<M: Money>(
    env: &Enviroment,
    state: &mut State<M>,
    input: &InputContent<M>,
    cases: Vec<Case<M>>,
) -> ApplyResult<M> {
    for case in cases {
        match apply_action(env, state, input, &case.action) {
            Some(warning) => return Some((warning, case.contract)),
            None => continue,
        }
    }
    None
}

fn apply_input<M: Money>(
    env: &Enviroment,
    state: &mut State<M>,
    input: &InputContent<M>,
    contract: Box<Contract<M>>,
) -> ApplyResult<M> {
    match *contract {
        Contract::When(cases, _, _) => apply_cases(env, state, input, cases),
        Contract::Pay(_, _, _, _, _) => None,
        Contract::Close => None,
    }
}

enum ApplyAllError {
    ApplyAllNoMatch,
    ApplyAllAmbiguousTimeInterval,
}

#[derive(Debug, Clone, Copy)]
enum TransactionWarning {
    Apply(ApplyWarning),
    Reduce(ReduceWarning),
}

impl From<ReduceWarning> for TransactionWarning {
    fn from(value: ReduceWarning) -> Self {
        TransactionWarning::Reduce(value)
    }
}

impl From<ApplyWarning> for TransactionWarning {
    fn from(value: ApplyWarning) -> Self {
        TransactionWarning::Apply(value)
    }
}

struct ApplyAllSuccess<M: Money> {
    is_reduced: bool,
    warnings: Vec<TransactionWarning>,
    payments: Vec<Payment<M>>,
    contract: Contract<M>,
}

impl From<ReduceError> for ApplyAllError {
    fn from(_: ReduceError) -> Self {
        ApplyAllError::ApplyAllAmbiguousTimeInterval
    }
}

type ApplyAllResult<M: Money> = Result<ApplyAllSuccess<M>, ApplyAllError>;

/// Apply a list of Inputs to the contract after reduction
fn apply_all_inputs<M: Money>(
    env: &Enviroment,
    state: &mut State<M>,
    contract: Contract<M>,
    inputs: &mut Vec<InputContent<M>>,
) -> ApplyAllResult<M> {

    fn apply_all_loop<M: Money>(env: &Enviroment, state: &mut State<M>, inputs: &mut Vec<InputContent<M>>, all_warnings: &mut Vec<TransactionWarning>, all_payments: &mut Vec<Payment<M>>, reduced: bool, contract: Box<Contract<M>>) -> ApplyAllResult<M>{
        match reduce_contract_until_quiescent(env, state, contract) {
            Ok(ContractQuiescent {
                is_reduced,
                warnings,
                payments,
                contract,
            }) => {
                //let mut reduced_contract = contract;
                all_warnings.extend(warnings.iter().map(|&x| TransactionWarning::Reduce(x)));
                all_payments.extend(payments);
                match inputs.pop() {
                    None => {
                        let warnings: Vec<TransactionWarning> = all_warnings.iter().map(|x| (*x).clone()).collect();
                        let payments: Vec<Payment<M>> = all_payments.iter().map(|x| (*x).clone()).collect();
                        return Ok(ApplyAllSuccess {
                            is_reduced: reduced || is_reduced,
                            warnings,
                            payments,
                            contract: *contract,
                        })
                    }
                    Some(input) => {
                        let (warning, cont) = apply_input(env, state, &input, contract).ok_or(ApplyAllError::ApplyAllNoMatch)?;
                        all_warnings.push(warning.into());
                        apply_all_loop(env, state, inputs, all_warnings, all_payments, reduced || is_reduced, Box::new(cont))
                    }
                }
            }
            Err(e) => return Err(e.into()),
        }
    }
    let mut all_warnings: Vec<TransactionWarning> = Vec::new();
    let mut all_payments = Vec::new();
    apply_all_loop(env, state, inputs, &mut all_warnings, &mut all_payments, false, Box::new(contract))
}

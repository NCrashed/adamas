//! Временный зонд для §10 вопроса 134. Не коммитить.

use adamas_core::sig::Signature;
use adamas_elab::elaborate;
use adamas_parser::parse;

fn program(text: &str) -> Signature {
    let module = match parse(text) {
        Ok(module) => module,
        Err(error) => panic!("не разобралось: {error}"),
    };
    match elaborate(&module) {
        Ok((signature, _)) => signature,
        Err(error) => panic!("не элаборировалось: {error}"),
    }
}

const BASE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat
";

const DIVERGING: &str = "
data Wit (n : Nat) where
  Mk : Wit n

class Loop a where
  spin : a -> a

instance Loop Nat where
  spin n = spin n
";

#[test]
fn probe_current_state() {
    let signature = program(&format!(
        "{BASE}{DIVERGING}
use : Wit (spin Zero) -> Nat
use w = Zero
"
    ));
    for name in ["spin", "Loop#Nat", "Loop#Nat.spin", "use"] {
        let Some(d) = signature.lookup(name) else {
            eprintln!("{name}: НЕ НАЙДЕНО");
            continue;
        };
        eprintln!("=== {name}: total={}", d.total);
        if let Some(body) = &d.body {
            eprintln!("  body: {body:?}");
        }
    }
    panic!("dump — зонд, не тест");
}

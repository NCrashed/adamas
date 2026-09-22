//! Замер: какую глубину терма выдерживает поток с заданным стеком.
//!
//! Временный стенд трека D волны 4 Фазы 8. Снимается с дерева после замера.
//!
//! `depth_probe <стек-в-KiB> <форма> <N> <стадия>`
//!
//! Стадии: `parse`, `elab`, `eval`, `c`, `llvm`.

use std::thread;

fn nat_prelude() -> &'static str {
    "data Nat where\n  Zero : Nat\n  Succ : Nat -> Nat\n\n"
}

fn source(form: &str, n: usize) -> String {
    match form {
        // Унарный литерал: терм глубиной ровно N.
        "unary" => format!("{}main : Nat\nmain = {n}\n", nat_prelude()),
        // Написанная вложенность: спайн применений глубиной N.
        "nest" => {
            let mut body = String::from("0");
            for _ in 0..n {
                body = format!("(same {body})");
            }
            format!("same : UInt64 -> UInt64\nsame x = x\n\nmain : UInt64\nmain = {body}\n")
        }
        // Голые скобки: спуску по два входа на скобку, терму - ни одного звена.
        "paren" => {
            let body = format!("{}0{}", "(".repeat(n), ")".repeat(n));
            format!("main : UInt64\nmain = {body}\n")
        }
        // Строковый литерал: 3 звена на байт.
        "str" => format!(
            "text : Array {} UInt8\ntext = \"{}\"\n\nmain : UInt8\nmain = arrayIndex text 0\n",
            n + 1,
            "a".repeat(n)
        ),
        // Сумма: написанная вложенность D вокруг унарного литерала N.
        "sum" => {
            let (d, lit) = (n / 1000, n % 1000);
            let mut body = format!("{lit}");
            for _ in 0..d {
                body = format!("(same {body})");
            }
            format!(
                "{}same : Nat -> Nat\nsame x = x\n\nmain : Nat\nmain = {body}\n",
                nat_prelude()
            )
        }
        // Сумма: написанная вложенность D вокруг строки в K байт.
        "strsum" => {
            let (d, k) = (n / 1000, n % 1000);
            let mut body = format!("\"{}\"", "a".repeat(k));
            for _ in 0..d {
                body = format!("(same {body})");
            }
            format!(
                "same : Array {0} UInt8 -> Array {0} UInt8\nsame x = x\n\ntext : Array {0} UInt8\ntext = {body}\n\nmain : UInt8\nmain = arrayIndex text 0\n",
                k + 1
            )
        }
        // Список: `Cons` по звену на элемент.
        "list" => {
            let items = (0..n)
                .map(|_| "zero".to_owned())
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "data List a where\n  Nil : List a\n  Cons : a -> List a -> List a\n\nzero : UInt64\nzero = 0\n\nmain : List UInt64\nmain = [{items}]\n"
            )
        }
        // Блок: связывание на строку.
        "block" => {
            let mut body = String::new();
            for i in 0..n {
                body.push_str(&format!("  let x{i} : UInt64 = 0\n"));
            }
            body.push_str("  0\n");
            format!("main : UInt64\nmain =\n{body}")
        }
        // Стрелка: `Pi` на звено, и терм этот живёт в типе, а не в теле.
        "arrow" => {
            let domain = "UInt64 -> ".repeat(n);
            format!("odd : {domain}UInt64\n\nmain : UInt64\nmain = 0\n")
        }
        // Лямбда: `Lam` на параметр.
        "lam" => {
            let params = (0..n)
                .map(|i| format!("x{i}"))
                .collect::<Vec<_>>()
                .join(" ");
            let domain = "UInt64 -> ".repeat(n);
            format!(
                "zero : UInt64\nzero = 0\n\nodd : {domain}UInt64\nodd = \\{params} -> zero\n\nmain : UInt64\nmain = 0\n"
            )
        }
        // Кортеж: пара на звено.
        "tuple" => {
            let mut body = String::from("zero");
            let mut ty = String::from("UInt64");
            for _ in 0..n {
                body = format!("(zero, {body})");
                ty = format!("(UInt64, {ty})");
            }
            format!("zero : UInt64\nzero = 0\n\nmain : {ty}\nmain = {body}\n")
        }
        // Вложенный `if`: три подтерма на звено.
        "iff" => {
            let mut body = String::from("zero");
            for _ in 0..n {
                body = format!("(if yes then {body} else zero)");
            }
            format!(
                "data Bool where\n  True : Bool\n  False : Bool\n\nyes : Bool\nyes = True\n\nzero : UInt64\nzero = 0\n\nmain : UInt64\nmain = {body}\n"
            )
        }
        // Вложенный `if` в условии: типизируется, в отличие от вложения в ветвь.
        "ifcond" => {
            let mut cond = String::from("yes");
            for _ in 0..n {
                cond = format!("(if {cond} then yes else yes)");
            }
            format!(
                "data Bool where\n  True : Bool\n  False : Bool\n\nyes : Bool\nyes = True\n\nzero : UInt64\nzero = 0\n\nmain : UInt64\nmain = if {cond} then zero else zero\n"
            )
        }
        // Вложенный `case` блоком: разбор на звено, отступ на уровень.
        "casenest" => {
            let mut body = String::from("zero");
            for level in (0..n).rev() {
                let pad = "  ".repeat(level * 2 + 1);
                body =
                    format!("case yes of\n{pad}  True ->\n{pad}    {body}\n{pad}  False -> zero");
            }
            format!(
                "data Bool where\n  True : Bool\n  False : Bool\n\nyes : Bool\nyes = True\n\nzero : UInt64\nzero = 0\n\nmain : UInt64\nmain =\n  {body}\n"
            )
        }
        // Вложенный `case`: разбор на звено.
        "case" => {
            let mut body = String::from("zero");
            for _ in 0..n {
                body = format!("(case yes of\n    True -> {body}\n    False -> zero)");
            }
            format!(
                "data Bool where\n  True : Bool\n  False : Bool\n\nyes : Bool\nyes = True\n\nzero : UInt64\nzero = 0\n\nmain : UInt64\nmain = {body}\n"
            )
        }
        other => panic!("неизвестная форма {other}"),
    }
}

fn work(text: &str, stage: &str) -> String {
    use adamas_core::meta::Metas;
    use adamas_core::sig::Signature;
    use adamas_elab::class::Instances;
    use adamas_elab::fixity::Fixities;
    use adamas_elab::{Owned, Warnings};

    let module = match adamas_parser::parse(text) {
        Ok(module) => module,
        Err(error) => return format!("REFUSED-PARSE {error:?}"),
    };
    if stage == "parse" {
        return "OK".to_owned();
    }
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut instances = Instances::default();
    let mut fixities = Fixities::default();
    let mut warnings = Warnings::new();
    if let Err(error) = adamas_elab::elaborate_into(
        &module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut fixities,
        &mut instances,
        &mut warnings,
    ) {
        return format!("REFUSED-ELAB {error:?}");
    }
    if stage == "elab" {
        return "OK".to_owned();
    }
    let definition = match signature.lookup("main") {
        Some(found) => found,
        None => return "NO-MAIN".to_owned(),
    };
    let body = match &definition.body {
        Some(body) => body.clone(),
        None => return "NO-BODY".to_owned(),
    };
    if stage == "interp" {
        return match adamas_interp::run(&signature, &body) {
            Ok(_) => "OK".to_owned(),
            Err(error) => format!("REFUSED-EVAL {error:?}"),
        };
    }
    // Драйвер понижает **специализированное**, а не написанное.
    let made = match adamas_elab::mono::specialise(&mut signature, &mut metas, &instances, &body) {
        Ok(made) => made,
        Err(error) => return format!("REFUSED-MONO {error}"),
    };
    let body = made.term;
    match stage {
        "mono" => "OK".to_owned(),
        "c" => match adamas_codegen::compile(&signature, &body) {
            Ok(_) => "OK".to_owned(),
            Err(error) => format!("REFUSED-C {error:?}"),
        },
        "llvm" => match adamas_codegen::compile_llvm(&signature, &body) {
            Ok(_) => "OK".to_owned(),
            Err(error) => format!("REFUSED-LLVM {error:?}"),
        },
        other => panic!("неизвестная стадия {other}"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let kib: usize = args[1].parse().unwrap();
    let form = args[2].clone();
    let n: usize = args[3].parse().unwrap();
    let stage = args[4].clone();
    let text = source(&form, n);
    let handle = thread::Builder::new()
        .stack_size(kib * 1024)
        .spawn(move || work(&text, &stage))
        .unwrap();
    match handle.join() {
        Ok(answer) => println!("{answer}"),
        Err(_) => println!("PANIC"),
    }
}

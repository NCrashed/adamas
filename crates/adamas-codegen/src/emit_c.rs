//! Эмиттер C: [`ir`](crate::ir) в переносимый C.
//!
//! **Ядра этот модуль не читает.** Он не знает ни узлов ядра, ни сигнатуры, ни
//! кратностей иначе как полем [`Fact`](crate::ir::Fact) - и это проверяемая
//! форма шва, а не пожелание: `tests/seam.rs` читает исходник этого файла и
//! требует, чтобы ядра в нём не упоминалось. LLVM-эмиттер Фазы 7 встанет рядом
//! и получит те же факты из того же места.
//!
//! # Что эмиттер с фактами делает
//!
//! Теряет - и это его работа. Кратность решает одно: эмитить связывание или
//! нет, потому что стёртого в рантайме нет вовсе (§3.3). Уникальность и регион
//! он не читает: в C сверх `restrict` выразить `noalias` нечем, а ставить его
//! наугад - хуже, чем не ставить. Существенно, что факты **есть** и потеряны
//! последним шагом.
//!
//! # Что получается на выходе
//!
//! Одна единица трансляции: таблица конструкторов, печать, объявления, функции,
//! точка входа. Всё `static`, кроме `main`, - LTO и whole-program эмиссия
//! обещаны §13 и Фазой 7, и одним файлом они даются даром.
//!
//! Функция понижается **первой формой** (§13, 2026-09-08): обычная C-функция,
//! кадр на C-стеке, скрытых аргументов нет вовсе. Оба они - вектор evidence и
//! ручка стека - появляются только на границе замыкания, потому что граница эта
//! динамическая: какая из форм за указателем, место вызова не знает. Там они
//! идут `NULL`, и рантайм принимает `NULL` всюду, где их читает.
//!
//! # Чего в выходе нет
//!
//! `dup` и `drop` не эмитятся ни одного: вставляет их Perceus (волна 3), и
//! разовые `free` до него - работа, которую потом пришлось бы выковыривать.
//! Пока их нет, программа не освобождает ничего; счётчики рантайма печатают
//! это числом на stderr.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::ir::{Arm, Binding, Constructor, CtorId, Expr, Form, FuncId, Function, Program};

/// Печать значения по таблице конструкторов.
const PRINTER: &str = include_str!("print.c");

/// Точка входа: печать ответа и счётчики блоков.
const ENTRY: &str = include_str!("main.c");

/// Почему эмиссия отказала.
#[derive(Debug, thiserror::Error)]
pub enum EmitError {
    /// Функция понижается второй формой.
    ///
    /// Скрытых аргумента у неё два - вектор evidence и ручка стека
    /// продолжения, - а кадр живёт в куче. Эмиттер её не досочиняет: форма
    /// приходит из IR, а кода под неё здесь нет.
    #[error("`{function}` понижается второй формой: кадр в куче этим срезом не эмитится")]
    Detached {
        /// Чья функция.
        function: String,
    },
}

/// Собирает единицу трансляции.
///
/// # Errors
///
/// [`EmitError`] - форма понижения, которой эмиттер не знает.
pub fn emit(program: &Program) -> Result<String, EmitError> {
    for function in &program.functions {
        if function.form == Form::Detached {
            return Err(EmitError::Detached {
                function: function.name.clone(),
            });
        }
    }
    let mut out = String::new();
    preamble(&mut out);
    table(&mut out, program);
    out.push_str(PRINTER);
    out.push('\n');

    let boxed = wrapped(program);
    let built = builders(program);

    out.push_str("/* Объявления: рекурсия и взаимная рекурсия видят друг друга. */\n");
    for function in &program.functions {
        let _ = writeln!(out, "{};", signature(function));
    }
    for tag in &built {
        let _ = writeln!(out, "{};", trampoline(&format!("make_{}", tag.0)));
    }
    for id in &boxed {
        let _ = writeln!(out, "{};", trampoline(&format!("box_{}", id.0)));
    }
    out.push('\n');

    for constructor in &program.constructors {
        if built.contains(&constructor.tag) {
            builder(&mut out, constructor);
        }
    }
    for function in &program.functions {
        body(&mut out, program, function);
        if boxed.contains(&function.id) {
            wrapper(&mut out, function);
        }
    }

    let _ = writeln!(out, "#define ADAMAS_ENTRY fn_{}\n", program.entry.0);
    out.push_str(ENTRY);
    Ok(out)
}

/// Заголовок единицы трансляции.
fn preamble(out: &mut String) {
    out.push_str(concat!(
        "/* Порождено понижением Adamas. Править нечего: правится тот, кто породил.\n",
        " *\n",
        " * Договор с рантаймом - `adamas.h`; форма значения, владение и кадры\n",
        " * описаны там. Здесь только код программы.\n",
        " */\n",
        "\n",
        "#include \"adamas.h\"\n",
        "\n",
        "#include <stdio.h>\n",
        "\n",
        "/* Стёртая позиция (§3.3): значения в рантайме нет. Макрос стоит там, где\n",
        " * стёртое связывание всё-таки упомянули бы, и печатается заметно. */\n",
        "#define ADAMAS_ERASED adamas_con0(0xFFFCu)\n",
        "\n",
    ));
}

/// Таблица конструкторов: имя и число полей по тегу.
fn table(out: &mut String, program: &Program) {
    out.push_str(concat!(
        "/* Конструкторы программы по тегу. Хвостовой элемент - чтобы массив не\n",
        " * оказался пустым у программы без единого конструктора. */\n",
    ));
    let _ = writeln!(
        out,
        "#define ADAMAS_CONSTRUCTORS {}u",
        program.constructors.len()
    );
    out.push_str("static const char *const adamas_con_name[] = {\n");
    for constructor in &program.constructors {
        let _ = writeln!(
            out,
            "    \"{}\", /* {} */",
            escaped(&constructor.name),
            escaped(&constructor.data)
        );
    }
    out.push_str("    \"\"\n};\n\nstatic const uint16_t adamas_con_slots[] = {\n");
    for constructor in &program.constructors {
        let _ = writeln!(out, "    {}u,", constructor.slots());
    }
    out.push_str("    0u\n};\n\n");
}

/// Номера функций, которым нужен трамплин: они где-то стоят значением.
fn wrapped(program: &Program) -> BTreeSet<FuncId> {
    let mut found = BTreeSet::new();
    for function in &program.functions {
        walk(&function.body, &mut |expr| {
            if let Expr::Closure { function, .. } = expr {
                found.insert(*function);
            }
        });
    }
    found
}

/// Теги конструкторов, которые где-то стоят значением.
fn builders(program: &Program) -> BTreeSet<CtorId> {
    let mut found = BTreeSet::new();
    for function in &program.functions {
        walk(&function.body, &mut |expr| {
            if let Expr::ConstructClosure { constructor } = expr {
                found.insert(*constructor);
            }
        });
    }
    found
}

/// Обход дерева выражения сверху вниз.
fn walk(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expr);
    match expr {
        Expr::Local(_) | Expr::Erased | Expr::ConstructClosure { .. } => {}
        Expr::Construct { arguments, .. } | Expr::Call { arguments, .. } => {
            for argument in arguments {
                walk(argument, visit);
            }
        }
        Expr::Closure { captured, .. } => {
            for capture in captured {
                walk(capture, visit);
            }
        }
        Expr::Apply { callee, argument } => {
            walk(callee, visit);
            walk(argument, visit);
        }
        Expr::Bind { value, body, .. } => {
            walk(value, visit);
            walk(body, visit);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            walk(scrutinee, visit);
            for arm in arms {
                walk(&arm.body, visit);
            }
        }
    }
}

/// Сигнатура функции: скрытые аргументы формы и живые связывания.
///
/// У первой формы скрытых нет **вовсе** (`adamas_lowered_first`): написанное и
/// есть всё. Захваченная среда сюда приходит обычными параметрами - трамплин
/// достаёт её из слотов замыкания и передаёт явно. Второй формы здесь не
/// бывает: [`emit`] отвергает её раньше.
fn signature(function: &Function) -> String {
    let live: Vec<String> = function
        .live_captured()
        .chain(function.live_parameters())
        .map(|binding| format!("adamas_value v{}", binding.local.0))
        .collect();
    let taken = if live.is_empty() {
        "void".to_owned()
    } else {
        live.join(", ")
    };
    format!("static adamas_value fn_{}({taken})", function.id.0)
}

/// Сигнатура трамплина: каноническая форма кода замыкания из `adamas.h`.
///
/// Скрытые аргументы у неё оба, потому что граница замыкания **динамическая**:
/// какая из двух форм за указателем, место вызова не знает. Тело первой формы
/// их не смотрит, и обещание «первая форма не платит ничего» держится там, где
/// вызываемый известен статически, - на прямом вызове.
fn trampoline(name: &str) -> String {
    format!(
        "static adamas_value {name}(adamas_value self, const adamas_evidence *ev, \
         adamas_kont *kont, adamas_value arg)"
    )
}

/// Тело функции.
fn body(out: &mut String, program: &Program, function: &Function) {
    let _ = writeln!(out, "/* {} */", escaped(&function.name));
    let _ = writeln!(out, "{} {{", signature(function));
    for binding in function.live_captured().chain(function.live_parameters()) {
        let _ = writeln!(
            out,
            "    /* v{} - {} */",
            binding.local.0,
            escaped(&binding.name)
        );
    }
    let mut emitter = Emitter {
        program,
        out: String::new(),
        temps: 0,
    };
    let answer = emitter.value(&function.body, 1);
    out.push_str(&emitter.out);
    let _ = writeln!(out, "    return {answer};\n}}\n");
}

/// Трамплин: замыкание отдаёт слоты позиционно, функция берёт их аргументами.
fn wrapper(out: &mut String, function: &Function) {
    let captured: Vec<&Binding> = function.live_captured().collect();
    let parameters: Vec<&Binding> = function.live_parameters().collect();
    let _ = writeln!(
        out,
        "/* `{}` значением: слоты - среда, затем накопленные аргументы. */",
        escaped(&function.name)
    );
    let _ = writeln!(out, "{} {{", trampoline(&format!("box_{}", function.id.0)));
    if parameters.is_empty() {
        out.push_str("    adamas_fail(\"замыкание без параметров\");\n}\n\n");
        return;
    }
    let mut taken: Vec<String> = (0..captured.len() + parameters.len() - 1)
        .map(|slot| format!("adamas_closure_get(self, {slot})"))
        .collect();
    taken.push("arg".to_owned());
    let _ = writeln!(
        out,
        "    return fn_{}({});\n}}\n",
        function.id.0,
        taken.join(", ")
    );
}

/// Сборщик конструктора: замыкание копит аргументы, последний собирает объект.
fn builder(out: &mut String, constructor: &Constructor) {
    let slots = constructor.slots();
    let _ = writeln!(out, "/* `{}` значением. */", escaped(&constructor.name));
    let _ = writeln!(
        out,
        "{} {{",
        trampoline(&format!("make_{}", constructor.tag.0))
    );
    if slots == 0 {
        out.push_str("    adamas_fail(\"конструктор без полей значением\");\n}\n\n");
        return;
    }
    let _ = writeln!(
        out,
        "    adamas_value value = adamas_alloc({}u, {slots}u);",
        constructor.tag.0
    );
    for slot in 0..slots - 1 {
        let _ = writeln!(
            out,
            "    adamas_set_field(value, {slot}, adamas_closure_get(self, {slot}));"
        );
    }
    let _ = writeln!(out, "    adamas_set_field(value, {}, arg);", slots - 1);
    out.push_str("    return value;\n}\n\n");
}

/// Состояние эмиссии одного тела.
struct Emitter<'a> {
    program: &'a Program,
    out: String,
    temps: u32,
}

impl Emitter<'_> {
    /// Свежее временное имя.
    fn temp(&mut self) -> String {
        let name = format!("t{}", self.temps);
        self.temps += 1;
        name
    }

    /// Отступ уровня `depth`.
    fn pad(depth: usize) -> String {
        "    ".repeat(depth)
    }

    /// Эмитит выражение и отдаёт имя, в котором лежит его значение.
    ///
    /// Каждый составной узел получает своё имя: порядок вычисления виден в
    /// тексте, а не выводится из правил C.
    fn value(&mut self, expr: &Expr, depth: usize) -> String {
        let pad = Self::pad(depth);
        match expr {
            Expr::Local(local) => format!("v{}", local.0),
            Expr::Erased => "ADAMAS_ERASED".to_owned(),
            Expr::Construct {
                constructor,
                arguments,
            } => self.construct(*constructor, arguments, depth),
            Expr::ConstructClosure { constructor } => {
                let described = &self.program.constructors[usize::from(constructor.0)];
                let name = self.temp();
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_value {name} = adamas_closure(make_{}, NULL, {}u, 0u); /* {} */",
                    constructor.0,
                    described.slots(),
                    escaped(&described.name)
                );
                name
            }
            Expr::Call {
                function,
                arguments,
            } => self.call(*function, arguments, depth),
            Expr::Closure { function, captured } => self.closure(*function, captured, depth),
            Expr::Apply { callee, argument } => {
                let callee = self.value(callee, depth);
                let argument = self.value(argument, depth);
                let name = self.temp();
                // Оба скрытых аргумента пусты: хендлеров в чистом фрагменте нет,
                // а `NULL` рантайм принимает всюду, где их читает.
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_value {name} = adamas_apply({callee}, NULL, NULL, {argument});"
                );
                name
            }
            Expr::Bind {
                binding,
                value,
                body,
            } => {
                let value = self.value(value, depth);
                let _ = writeln!(
                    self.out,
                    "{pad}adamas_value v{} = {value}; /* {} */",
                    binding.local.0,
                    escaped(&binding.name)
                );
                self.value(body, depth)
            }
            Expr::Match {
                scrutinee, arms, ..
            } => self.analysis(scrutinee, arms, depth),
        }
    }

    /// Объект конструктора: сперва аргументы, потом блок.
    fn construct(&mut self, constructor: CtorId, arguments: &[Expr], depth: usize) -> String {
        let pad = Self::pad(depth);
        let described = &self.program.constructors[usize::from(constructor.0)];
        let slots = described.slots();
        let title = escaped(&described.name);
        let present: Vec<usize> = described
            .binders
            .iter()
            .enumerate()
            .filter(|(_, fact)| fact.present)
            .map(|(position, _)| position)
            .collect();
        let given: Vec<String> = present
            .iter()
            .filter_map(|position| arguments.get(*position))
            .map(|argument| self.value(argument, depth))
            .collect();
        let name = self.temp();
        if slots == 0 {
            let _ = writeln!(
                self.out,
                "{pad}adamas_value {name} = adamas_con0({}u); /* {title} */",
                constructor.0
            );
            return name;
        }
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_alloc({}u, {slots}u); /* {title} */",
            constructor.0
        );
        for (slot, argument) in given.iter().enumerate() {
            let _ = writeln!(
                self.out,
                "{pad}adamas_set_field({name}, {slot}, {argument});"
            );
        }
        name
    }

    /// Прямой вызов: стёртые позиции в вызов не идут.
    fn call(&mut self, function: FuncId, arguments: &[Expr], depth: usize) -> String {
        let pad = Self::pad(depth);
        let called = &self.program.functions[function.0];
        let title = escaped(&called.name);
        let present: Vec<usize> = called
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, binding)| binding.fact.present)
            .map(|(position, _)| position)
            .collect();
        let given: Vec<String> = present
            .iter()
            .filter_map(|position| arguments.get(*position))
            .map(|argument| self.value(argument, depth))
            .collect();
        let name = self.temp();
        // Вызываемый известен статически, поэтому зовётся прямо и скрытых
        // аргументов не берёт вовсе (`adamas_lowered_first`).
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = fn_{}({}); /* {title} */",
            function.0,
            given.join(", ")
        );
        name
    }

    /// Замыкание: код плюс среда по слотам.
    fn closure(&mut self, function: FuncId, captured: &[Expr], depth: usize) -> String {
        let pad = Self::pad(depth);
        let described = &self.program.functions[function.0];
        let title = escaped(&described.name);
        let arity = described.live_parameters().count();
        let present: Vec<usize> = described
            .captured
            .iter()
            .enumerate()
            .filter(|(_, binding)| binding.fact.present)
            .map(|(position, _)| position)
            .collect();
        let taken: Vec<String> = present
            .iter()
            .filter_map(|position| captured.get(*position))
            .map(|capture| self.value(capture, depth))
            .collect();
        let name = self.temp();
        let _ = writeln!(
            self.out,
            "{pad}adamas_value {name} = adamas_closure(box_{}, NULL, {arity}u, {}u); /* {title} */",
            function.0,
            taken.len()
        );
        for (slot, capture) in taken.iter().enumerate() {
            let _ = writeln!(
                self.out,
                "{pad}adamas_closure_set({name}, {slot}, {capture});"
            );
        }
        name
    }

    /// Разбор: `switch` по тегу заголовка.
    fn analysis(&mut self, scrutinee: &Expr, arms: &[Arm], depth: usize) -> String {
        let pad = Self::pad(depth);
        let scrutinee = self.value(scrutinee, depth);
        let name = self.temp();
        let _ = writeln!(self.out, "{pad}adamas_value {name};");
        let _ = writeln!(self.out, "{pad}switch (adamas_tag({scrutinee})) {{");
        for arm in arms {
            let described = &self.program.constructors[usize::from(arm.constructor.0)];
            let title = escaped(&described.name);
            let params = described.params as usize;
            let slots: Vec<Option<u32>> = (0..arm.fields.len())
                .map(|position| described.slot(params + position))
                .collect();
            let _ = writeln!(
                self.out,
                "{pad}case {}u: {{ /* {title} */",
                arm.constructor.0
            );
            for (binding, slot) in arm.fields.iter().zip(&slots) {
                if let Some(slot) = slot {
                    let _ = writeln!(
                        self.out,
                        "{pad}    adamas_value v{} = adamas_field({scrutinee}, {slot}); /* {} */",
                        binding.local.0,
                        escaped(&binding.name)
                    );
                }
            }
            let answer = self.value(&arm.body, depth + 1);
            let _ = writeln!(self.out, "{pad}    {name} = {answer};");
            let _ = writeln!(self.out, "{pad}    break;");
            let _ = writeln!(self.out, "{pad}}}");
        }
        let _ = writeln!(
            self.out,
            "{pad}default: adamas_fail(\"разбор не знает конструктора\");"
        );
        let _ = writeln!(self.out, "{pad}}}");
        name
    }
}

/// Строка, годная внутрь C-литерала и комментария.
///
/// Имена в Adamas бывают операторами и путями (`+`, `Boxes.Wrap`), и печатает
/// их ответ программы. Небезопасны из них ровно три знака: кавычка и слэш
/// ломают литерал, `*/` закрывает комментарий раньше времени.
fn escaped(name: &str) -> String {
    name.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace("*/", "* /")
}

//! Хендлер и операция без снятия сегмента (трек B волны 4, §3.4).
//!
//! Корпус (`tests/agreement.rs`) отвечает за то, что понижение считает то же,
//! что машина. Здесь стоит то, чего корпус не различает: **порядок** и
//! **выбор**. Обе формы ошибки сокращаются на симметричном пути - переставь
//! записи вектора, слоты среды или номера веток, и программа со сложением
//! ответит тем же числом. Поэтому каждый свидетель здесь отвечает **списком**,
//! а не суммой, и каждый снят мутантом.
//!
//! Что называется по имени, а не молчит: общая ветка (трек D), мультишот
//! (трек E), параметризованный хендлер (трек D) и маска. Абортивная ветка
//! отсюда ушла - её берёт трек C, и свидетели её в `abortive.rs`.

mod harness;

/// Общая шапка: список, число и метка с одной операцией.
const SHAPE: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

effect Ask where
  ask : Nat
";

/// Ответ программы по мнению машины и по мнению понижения - они же сверены.
fn run(name: &str, source: &str) -> (String, usize) {
    let answer = harness::printed(source);
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    (answer, allocated)
}

/// Два одноимённых хендлера: операция достаётся **внутреннему**.
///
/// Так читается правило погашения §3.4: `{Ask} ⊑ {Ask, Ask}` отдаёт вызываемому
/// внутреннее вхождение, поэтому смещение вектора всегда нуль, а поиск идёт
/// изнутри наружу. Число пропусков (`skip` у `adamas_evidence_lookup`) здесь
/// нуль, и наблюдаем он именно этим: сойдись порядок записей наоборот - ответил
/// бы внешний.
///
/// Записи живут в векторе одновременно, а не по очереди: вычисление объявлено с
/// двумя `Ask` в row, и внутренний хендлер снимает одну из двух.
const NESTED: &str = "\
twice : {Ask, Ask} Nat
twice = ask

near : {Ask} Nat
near = handle twice with
  return v -> v
  ask -> resume (Succ Zero)

main : Nat
main = handle near with
  return v -> v
  ask -> resume Zero
";

#[test]
fn the_innermost_handler_of_two_alike_answers() {
    let (answer, _) = run("одноимённые", &format!("{SHAPE}{NESTED}"));
    assert_eq!(
        answer, "Succ Zero",
        "операцию поймал внешний хендлер: поиск в векторе идёт не изнутри наружу"
    );
}

/// Среда веток: слоты кадра держат порядок захвата.
///
/// Ответ - список из трёх различных чисел, и переставленные слоты меняют его,
/// а не оставляют тем же. Сложение здесь не годилось бы: оно коммутативно, и
/// перестановка на нём ненаблюдаема - тот же довод, каким написан свидетель
/// захватов замыкания в `agreement.rs`.
const CAPTURES: &str = "\
asked : {Ask} Nat
asked = ask

paired : Nat -> Nat -> List Nat
paired a b = handle asked with
  return v -> Cons v (Cons a (Cons b Nil))
  ask -> resume Zero

main : List Nat
main = paired (Succ Zero) (Succ (Succ (Succ Zero)))
";

#[test]
fn the_frame_environment_keeps_the_order_of_its_slots() {
    let (answer, _) = run("среда", &format!("{SHAPE}{CAPTURES}"));
    assert_eq!(
        answer, "Cons Zero (Cons (Succ Zero) (Cons (Succ (Succ (Succ Zero))) Nil))",
        "слоты среды кадра переставлены"
    );
}

/// Номер операции выбирает ветку, а `return` идёт своим номером.
///
/// Метка с двумя операциями и `return`, который **не** тождествен: три разные
/// работы, и ответ различает все три. Сойдись номера веток - список вышел бы
/// другим.
const BRANCHES: &str = "\
effect Two where
  first : Nat
  second : Nat

asked : {Two} (List Nat)
asked = Cons first (Cons second Nil)

main : List Nat
main = handle asked with
  return v -> Cons (Succ (Succ Zero)) v
  first -> resume Zero
  second -> resume (Succ Zero)
";

#[test]
fn the_operation_number_picks_the_branch() {
    let (answer, _) = run("ветки", &format!("{SHAPE}{BRANCHES}"));
    assert_eq!(
        answer, "Cons (Succ (Succ Zero)) (Cons Zero (Cons (Succ Zero) Nil))",
        "ветка выбрана не своим номером либо `return` не сработал"
    );
}

/// Аргументы операции доезжают до ветки в написанном порядке.
const ARGUMENTS: &str = "\
effect Tell where
  tell : Nat -> Nat -> List Nat

asked : {Tell} (List Nat)
asked = tell Zero (Succ Zero)

main : List Nat
main = handle asked with
  return v -> v
  tell x y -> resume (Cons y (Cons x Nil))
";

#[test]
fn the_arguments_of_an_operation_keep_their_order() {
    let (answer, _) = run("аргументы", &format!("{SHAPE}{ARGUMENTS}"));
    assert_eq!(
        answer, "Cons (Succ Zero) (Cons Zero Nil)",
        "аргументы операции пришли ветке не в том порядке"
    );
}

/// Хендлер глубокий: операция после возобновления попадает **тому же**.
///
/// Кадр остаётся на стеке - хвостовая резумпция сегмента не снимает, - и это
/// то самое место, где «глубокий» ничего не стоит. Три операции подряд: одной
/// хватило бы и мелкому.
const DEEP: &str = "\
thrice : {Ask} (List Nat)
thrice = Cons ask (Cons ask (Cons ask Nil))

main : List Nat
main = handle thrice with
  return v -> v
  ask -> resume (Succ Zero)
";

#[test]
fn the_handler_survives_its_first_operation() {
    let (answer, _) = run("глубокий", &format!("{SHAPE}{DEEP}"));
    assert_eq!(
        answer, "Cons (Succ Zero) (Cons (Succ Zero) (Cons (Succ Zero) Nil))",
        "хендлер не пережил первой операции"
    );
}

/// Ветка работает под вектором **места `handle`**, а не операции.
///
/// Окружающая ветки есть окружающая применения хендлера (§3.4), поэтому `ask`
/// внутри ветки уходит наружу - внешнему хендлеру, - а не своему. Свидетель
/// строгий: возьми ветка вектор операции, и она позвала бы саму себя.
const RELAY: &str = "\
asked : {Ask} Nat
asked = ask

relayed : {Ask} Nat
relayed = handle asked with
  return v -> v
  ask -> resume (Succ ask)

main : Nat
main = handle relayed with
  return v -> v
  ask -> resume Zero
";

#[test]
fn a_branch_reaches_past_its_own_handler() {
    let (answer, _) = run("переизлучение", &format!("{SHAPE}{RELAY}"));
    assert_eq!(
        answer, "Succ Zero",
        "операция ветки ушла не к внешнему хендлеру"
    );
}

/// Хендлер в чистой функции: она корень своего стека, и течи нет.
///
/// `runIO`-семейство корпуса устроено так же: row погашена внутри, наружу не
/// уходит ничего, скрытых аргументов у функции нет. Проверяется здесь то, чего
/// корпус не показывает числом, - что кадр, вектор и корень возвращены куче.
const ROOTED: &str = "\
asked : {Ask} Nat
asked = ask

runAsk : {a : Type} -> ((ω u : Unit) -> {Ask} a) -> a
runAsk k = handle k with
  return v -> v
  ask -> resume (Succ Zero)

body : (ω u : Unit) -> {Ask} (List Nat)
body u = Cons ask (Cons ask Nil)

main : List Nat
main = runAsk body
";

#[test]
fn a_pure_function_roots_its_own_stack() {
    let (answer, allocated) = run("корень", &format!("{SHAPE}{ROOTED}"));
    assert_eq!(answer, "Cons (Succ Zero) (Cons (Succ Zero) Nil)");
    // Восемь, и каждый назван: две ячейки `Cons`, два `Succ` (ветка отвечает
    // дважды), замыкание `body`, кадр хендлера и два вектора evidence - пустой
    // корень чистой `runAsk` и расширенный им. Три последних и есть цена
    // второй формы; снимет её §10 вопрос 74.
    assert_eq!(allocated, 8, "цена хендлера в блоках изменилась");
}

/// Общая ветка отвергается **по имени**, со ссылкой на трек D.
#[test]
fn a_general_branch_is_refused_by_name() {
    let source = format!(
        "{SHAPE}\
asked : {{Ask}} (List Nat)
asked = Cons ask Nil

main : List Nat
main = handle asked with
  return v -> v
  ask -> Cons Zero (resume Zero)
"
    );
    let error = harness::compiled(&source).expect_err("одношот общего вида - трек D");
    let text = error.to_string();
    assert!(
        text.contains("ветка `ask` хендлера `Ask`") && text.contains("трек D"),
        "отказ не назвал ни ветку, ни трек: {text}"
    );
}

/// Мультишот отвергается по имени, со ссылкой на трек E.
#[test]
fn a_multishot_handler_is_refused_by_name() {
    let source = format!(
        "{SHAPE}\
asked : {{Ask}} Nat
asked = ask

main : Nat
main = handleMulti asked with
  return v -> v
  ask -> resume Zero
"
    );
    let error = harness::compiled(&source).expect_err("мультишот - трек E");
    let text = error.to_string();
    assert!(
        text.contains("#handleMulti.Ask") && text.contains("трек E"),
        "отказ не назвал ни элиминатор, ни трек: {text}"
    );
}

/// Операция в функции с плоским ответом отвергается: обрыв вернуть нечем.
///
/// Вердикт `SUPPRESSED` требует вернуть ответ `adamas_kont_abort` немедленно
/// (`adamas.h`), а ответ этот - значение. Функция, отдающая `int64_t`, вернуть
/// его не может, и отказ здесь лучше порождённого C, который не соберётся.
/// Граница та же, что у прочего плоского на границах (§4.11), и снимет её
/// боксирование (§5.1).
///
/// Свидетель обходит хендлер: под ним плоское вычисление отвергается раньше,
/// на своём месте, а здесь плоский ответ уезжает через чистого соседа.
#[test]
fn an_operation_needs_a_pointer_answer_to_abort_through() {
    let source = format!(
        "{SHAPE}\
widen : Nat -> Int64
widen Zero = 0
widen (Succ k) = addInt64 (widen k) 1

sized : (ω u : Unit) -> {{Ask}} Int64
sized u = widen ask

narrow : Int64 -> Nat
narrow n = Zero

outer : (ω u : Unit) -> {{Ask}} Nat
outer u = narrow (sized u)

main : Nat
main = handle outer with
  return v -> v
  ask -> resume (Succ Zero)
"
    );
    let error = harness::compiled(&source).expect_err("обрыв плоским ответом не возвращается");
    let text = error.to_string();
    assert!(
        text.contains("`sized`") && text.contains("плоским ответом"),
        "отказ не назвал ни функции, ни причины: {text}"
    );
}

/// Питомник отвергается **своим** отказом, а не чужим.
///
/// Пока отказ был один на всё эффектное, остаток волны и остаток Фазы 7 стояли
/// под одним именем. `adamas.h` говорит прямо: метка `NURSERY` не обслуживается
/// ничем, таблица файберов заводится вместе с ними. Значит и отказ у неё свой,
/// иначе Фаза 7 замаскируется под недоделку понижения.
#[test]
fn a_nursery_is_refused_as_a_nursery() {
    let source = format!(
        "{SHAPE}\
effect Async where
  suspend : Unit

-- Постулат: тело ему даёт машина, а рантайм C - нет.
withNursery : ({{Async}} Nat) -> Nat

quiet : {{Async}} Nat
quiet = Zero

main : Nat
main = withNursery quiet
"
    );
    let error = harness::compiled(&source).expect_err("питомник - Фаза 7");
    let text = error.to_string();
    assert!(
        text.contains("питомник") && text.contains("Фаза 7"),
        "отказ не назвал ни питомника, ни фазы: {text}"
    );
}

/// Маска отвергается по имени: число пропусков вектору не считает никто.
#[test]
fn a_mask_is_refused_by_name() {
    let source = format!(
        "{SHAPE}\
asked : {{Ask}} Nat
asked = ask

masked : {{Ask, Ask}} Nat
masked = mask asked

near : {{Ask}} Nat
near = handle masked with
  return v -> v
  ask -> resume (Succ Zero)

main : Nat
main = handle near with
  return v -> v
  ask -> resume Zero
"
    );
    let error = harness::compiled(&source).expect_err("маска этим срезом не берётся");
    let text = error.to_string();
    assert!(
        text.contains("#mask.Ask") && text.contains("маска"),
        "отказ не назвал маску: {text}"
    );
}

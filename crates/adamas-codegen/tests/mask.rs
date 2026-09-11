//! Маска: вектор без ближайшей записи своей метки (§3.4, §10 вопрос 72).
//!
//! Корпус (`tests/agreement.rs`) отвечает за то, что понижение считает то же,
//! что машина, и `eval/mask.adamas` уже говорит про сам язык. Здесь стоит то,
//! чего корпус не различает, и различий этих три жанра.
//!
//! **Маска против её отсутствия.** Одна и та же программа в двух видах,
//! отличающихся ровно словом `mask`. Без этой пары «маска работает» проверялось
//! бы утверждением про один прогон, а прогон без маски отвечал бы тем же, если
//! бы маска не делала ничего.
//!
//! **Ответы позиционны.** Два одноимённых хендлера с **разными** ответами и
//! список вместо суммы: `0 + 1` и `1 + 0` совпадают, и маска, наехавшая не на
//! ту запись, прошла бы незамеченной. Тот же довод записан в шапке
//! `eval/mask.adamas`, и он же - причина, по которой каждый свидетель здесь
//! отвечает списком.
//!
//! **Цена и место.** Маска стоит **вектора, а не кадра**, и это наблюдаемо
//! числом блоков: разница масочной программы с безмасочной ровно одна ячейка на
//! маску - у обеих форм эмиттера, и хвостовой, и значение-формы. Место же её -
//! точка `mask`, а не точка операции, и различает эти два прочтения хендлер,
//! поставленный **внутри** маскируемого вычисления.
//!
//! Последним стоит свидетель не маски, а того, что маску держало: резумпция в
//! слоте замыкания. Нашёл его capstone, и место ему здесь - в файле того среза,
//! который capstone взял.

mod harness;

/// Общая шапка: список, число, единица и метка с одной операцией.
const SHAPE: &str = "\
data Bool where
  False : Bool
  True : Bool

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

/// Два запроса под вложенными одноимёнными хендлерами; второй написан маской.
///
/// `{written}` подставляется словом `mask` либо пустотой - больше программы не
/// различаются ничем.
///
/// Ответ хендлера - нульарный конструктор, а не число: сравниваются здесь **и**
/// ответы, **и** цена, а `Succ Zero` против `Zero` стоил бы лишней ячейки, и
/// разница в блоках говорила бы про ответ, а не про маску. `Near` и `Far` -
/// непосредственные значения (§13, 2026-09-08), и обеим программам они стоят
/// поровну.
fn layered(written: &str) -> String {
    format!(
        "{SHAPE}\
data Side where
  Near : Side
  Far : Side

effect Which where
  which : Side

asked : {{Which, Which}} List Side
asked =
  let near : Side = which
  let far : Side = {written} which
  Cons near (Cons far Nil)

inner : {{Which}} List Side
inner = handle asked with
  return v -> v
  which -> resume Near

main : List Side
main = handle inner with
  return v -> v
  which -> resume Far
"
    )
}

#[test]
fn a_mask_reaches_the_outer_handler_and_costs_a_vector() {
    let (masked, with_mask) = run("маска-есть", &layered("mask"));
    let (plain, without) = run("маска-нет", &layered(""));

    // Ответы позиционны: внутренний отвечает `Near`, внешний - `Far`.
    assert_eq!(
        masked, "Cons Near (Cons Far Nil)",
        "маска не дошла до внешнего хендлера"
    );
    assert_eq!(
        plain, "Cons Near (Cons Near Nil)",
        "без маски оба запроса обязаны достаться внутреннему"
    );

    // Цена названа числом: маска - вектор, и только он. Кадра у неё нет, и
    // разница в две ячейки означала бы, что кадр всё-таки ставится.
    assert_eq!(
        with_mask,
        without + 1,
        "маска стоит не одной ячейки: {with_mask} против {without}"
    );
}

/// Маска над **чистым** вычислением: вектор строится и отдаётся на месте.
///
/// Форм у маски в эмиттере две, и различает их точка приостановки: под
/// вычислением, которое не приостанавливается, маска остаётся значением и
/// отдаёт свой вектор тут же, а не эпилогом куска. Ответ здесь не различает
/// ничего - под маской операций нет вовсе, - и свидетельствуют цена и течь:
/// одна ячейка сверх безмасочной программы и ноль живых блоков. Без этого
/// свидетеля значение-форма не покрыта ни одним прогоном.
fn quiet(written: &str) -> String {
    format!(
        "{SHAPE}\
quietly : Nat
quietly = Succ (Succ Zero)

both : {{Ask, Ask}} List Nat
both =
  let a : Nat = ask
  let b : Nat = {written} quietly
  Cons a (Cons b Nil)

near : {{Ask}} List Nat
near = handle both with
  return v -> v
  ask -> resume Zero

main : List Nat
main = handle near with
  return v -> v
  ask -> resume (Succ Zero)
"
    )
}

#[test]
fn a_mask_over_a_pure_computation_gives_its_vector_back() {
    let (masked, with_mask) = run("маска-чистое", &quiet("mask"));
    let (plain, without) = run("маска-чистое-нет", &quiet(""));
    assert_eq!(masked, plain, "маска над чистым изменила ответ");
    assert_eq!(
        with_mask,
        without + 1,
        "значение-форма маски стоит не одной ячейки: {with_mask} против {without}"
    );
}

/// Снимается запись **своей** метки, а не просто ближайшая.
///
/// Между маской и её хендлером стоит хендлер **чужой** метки, и в векторе его
/// запись лежит последней. Мутант, снимающий последнюю запись без взгляда на
/// метку, переживает и корпус, и три прочих свидетеля этого файла: во всех них
/// последняя запись как раз своя, и различие сокращается. Здесь оно не
/// сокращается - `other` отвечает пятёркой, и снятие его записи увело бы `far`
/// обратно к внутреннему `Ask`.
const ALIEN: &str = "\
effect Other where
  other : Nat

inside : {Ask, Ask, Other} List Nat
inside =
  let o : Nat = other
  let near : Nat = ask
  let far : Nat = mask ask
  Cons o (Cons near (Cons far Nil))

withOther : {Ask, Ask} List Nat
withOther = handle inside with
  return v -> v
  other -> resume (Succ (Succ (Succ (Succ (Succ Zero)))))

nearAsk : {Ask} List Nat
nearAsk = handle withOther with
  return v -> v
  ask -> resume Zero

main : List Nat
main = handle nearAsk with
  return v -> v
  ask -> resume (Succ Zero)
";

#[test]
fn a_mask_takes_the_entry_of_its_own_label() {
    let (answer, _) = run("маска-чужая-метка", &format!("{SHAPE}{ALIEN}"));
    assert_eq!(
        answer, "Cons (Succ (Succ (Succ (Succ (Succ Zero))))) (Cons Zero (Cons (Succ Zero) Nil))",
        "маска сняла последнюю запись вектора, а не запись своей метки"
    );
}

/// Хендлер, поставленный **под** маской, ближе неё.
///
/// Этим различаются два прочтения маски: правка вектора в точке `mask` и счёт
/// пропусков в точке операции. Считай маска пропуски у операции - запрос внутри
/// `guarded` пропустил бы **его** хендлер и достался бы `near`, то есть ответил
/// бы `1` вместо `3`. Правка вектора отвечает `3`: запись `near` снята там, где
/// написана маска, а `guarded` встал уже поверх снятого.
const UNDER: &str = "\
twice : {Ask, Ask} Nat
twice = ask

guarded : {Ask} Nat
guarded = handle twice with
  return v -> v
  ask -> resume (Succ (Succ (Succ Zero)))

both : {Ask} List Nat
both =
  let a : Nat = guarded
  let b : Nat = ask
  Cons a (Cons b Nil)

past : {Ask, Ask} List Nat
past = mask both

near : {Ask} List Nat
near = handle past with
  return v -> v
  ask -> resume (Succ Zero)

main : List Nat
main = handle near with
  return v -> v
  ask -> resume (Succ (Succ Zero))
";

#[test]
fn a_handler_installed_under_the_mask_stands_nearer_than_it() {
    let (answer, _) = run("маска-под-хендлером", &format!("{SHAPE}{UNDER}"));
    assert_eq!(
        answer, "Cons (Succ (Succ (Succ Zero))) (Cons (Succ (Succ Zero)) Nil)",
        "маска сработала в точке операции, а не в точке `mask`"
    );
}

/// Маска переживает **точку приостановки**.
///
/// Вычисление под маской производит дважды, а ветка внешнего хендлера - общая:
/// сегмент режется, тело дробится кадрами, и второй запрос считается уже другим
/// куском C. Вектор маски своя ссылка того куска не переживает - её отдаёт
/// эпилог, - а кадры, положенные вычислением, берут свою и отдают её
/// продолжению (`adamas_frame_evidence`). Разъедься это - второй запрос
/// достался бы `near` и ответил бы `9`.
///
/// Ответ различает и порядок: `Cons Zero` дописывается веткой на каждом
/// возобновлении, а два `Succ Zero` приходят от запросов.
const ACROSS: &str = "\
both : {Ask} List Nat
both =
  let a : Nat = ask
  let b : Nat = ask
  Cons a (Cons b Nil)

past : {Ask, Ask} List Nat
past = mask both

near : {Ask} List Nat
near = handle past with
  return v -> v
  ask -> resume (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))))

main : List Nat
main = handle near with
  return v -> v
  ask -> Cons Zero (resume (Succ Zero))
";

#[test]
fn a_mask_holds_across_a_suspension_point() {
    let (answer, _) = run("маска-через-приостановку", &format!("{SHAPE}{ACROSS}"));
    assert_eq!(
        answer, "Cons Zero (Cons Zero (Cons (Succ Zero) (Cons (Succ Zero) Nil)))",
        "маска не пережила точку приостановки"
    );
}

/// Резумпция, не дожившая до возобновления, **раскручивается** и в слоте
/// замыкания (§3.4).
///
/// Нить состояния параметризованного хендлера держит резумпцию в замыкании
/// `\\s -> resume v s`; оборвись вычисление раньше применения - замыкание гибнет
/// вместе с ней, и сегмент её обязан раскрутиться, а не выброситься. Дропает
/// его там `adamas_release_value`, а ручки стека у неё нет по сигнатуре: точка
/// эта - `adamas_segment_abandon`, вторая из двух названных в `adamas.h`.
///
/// Наблюдаемо это деструктором ресурса, лежащего под нитью: без раскрутки он не
/// срабатывает вовсе, и отметка `9` из ответа пропадает. Живые блоки ловят то же
/// вторым счётом - сегмент остаётся висеть целиком.
///
/// Стоит здесь, а не в `general.rs`, потому что нашёл это capstone
/// `eval/interpreter.adamas`: там нить состояния, ресурс и обрыв встречаются
/// друг с другом, а поодиночке ни один свидетель этого не давал.
const ABANDONED: &str = "\
effect Fail where
  fail : Nat -> Nat

effect Env where
  look : Nat -> Nat

effect Trace where
  note : Nat -> Unit

lookupAt : Nat -> List Nat -> {Fail} Nat
lookupAt n Nil = fail n
lookupAt Zero (Cons x xs) = x
lookupAt (Succ k) (Cons x xs) = lookupAt k xs

resource Source where
  Open : Source
  close : (1 s : Source) -> {Trace} Bool
  close s =
    note (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))))
    True

guarded : Source -> {Env, Fail, Trace} Nat
guarded s =
  let u : Unit = note Zero
  look (Succ (Succ Zero))

opened : {Env, Fail, Trace} Nat
opened = guarded Open

threaded : {Fail, Trace} Nat
threaded = handle opened with
  state Nil
  return v -> v
  look i -> resume (lookupAt i state) state

recovered : {Trace} Nat
recovered = handle threaded with
  return v -> v
  fail e -> Zero

main : List Nat
main = handle recovered with
  return v -> Nil
  note n -> Cons n (resume MkUnit)
";

#[test]
fn a_resumption_left_in_a_closure_slot_unwinds() {
    let (answer, _) = run("брошенная-резумпция", &format!("{SHAPE}{ABANDONED}"));
    // Отметка деструктора обязана стоять в ответе **машины** тоже - иначе
    // свидетель мельче того, что проверяет, и `run` сверяет два молчания.
    assert_eq!(
        answer,
        "Cons Zero (Cons (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))) Nil)",
        "деструктор брошенной резумпции не сработал"
    );
}

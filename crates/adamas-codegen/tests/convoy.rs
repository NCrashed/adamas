//! Разбор с вынесенными соседями не строит замыкания (§10 вопрос 199).
//!
//! Соседи, чьи типы уточняет разбор, выносятся в мотив, и разбор применяется
//! обратно к ним - convoy-паттерн (`adamas-core/src/pattern.rs`). Ветвь
//! отвечает лямбдой по соседям. Понижение, видевшее в этом применение
//! значения, строило замыкание на каждый разбор, и новая ячейка ответа не
//! получала разобранной под переписывание: два блока на вызов.
//!
//! Записано это было утечкой стирания - «стёртый аргумент строится в
//! рантайме», - но построенным значением был не стёртый аргумент, а замыкание,
//! и стёртость соседа тут ни при чём: нестёртый сосед стоил того же. Свидетели
//! поэтому оба.
//!
//! Различает свидетель числом блоков на тысячу проходов, а не «прошло»:
//! программа считала верно и до починки.

mod harness;

/// Сколько блоков выдал прогон. Ответ по дороге сверяется с `adamas eval`.
fn allocated(name: &str, source: &str) -> usize {
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    allocated
}

/// Индекс, доказательство над ним и носитель того же индекса. `{proof}` -
/// кратность доказательства в сигнатуре `f`.
fn program(proof: &str) -> String {
    format!(
        "\
data T where
  A : T
  B : T -> T

data Proof : T -> Type where
  Yes : (0 x : T) -> Proof x

data Box : T -> Type where
  MkBox : (0 x : T) -> UInt64 -> Box x

big : T
big = B (B A)

evidence : Proof big
evidence = Yes big

f : (0 x : T) -> ({proof} p : Proof x) -> Box x -> Box x
f x p (MkBox d n) = MkBox x n

loop : Box big -> UInt64 -> Box big
loop b 0 = b
loop b n = loop (f big evidence b) (subUInt64 n 1)

peek : Box big -> UInt64
peek (MkBox d n) = n

main : UInt64
main = peek (loop (MkBox big 7) 1000)
"
    )
}

/// Стёртый сосед: форма из `docs/measurements/erased-leak/leak.adamas`.
///
/// Блок один - начальный `MkBox`; каждый проход переписывает разобранную
/// ячейку. До починки - 2001.
#[test]
fn an_erased_neighbour_costs_no_closure() {
    assert_eq!(allocated("convoy-erased", &program("0")), 1);
}

/// Нестёртый сосед: тот же разбор, та же цена.
#[test]
fn a_kept_neighbour_costs_no_closure() {
    assert_eq!(allocated("convoy-kept", &program("ω")), 1);
}

//! Массив в поле параметрического семейства (§4.11, §10 вопрос 210).
//!
//! Поле `Array n a` укладывается тем же правилом, что массив в позиции:
//! плоско там, где `a` известен плоским либо в контексте есть `{Flat a}`, и
//! указательно иначе. Слот поля указательный при любых ячейках - массив свой
//! объект кучи, - поэтому меняется не укладка конструктора, а взгляд на поле:
//! при постройке и при разборе он берётся у типа поля на месте.
//!
//! Граница та же, что у `same : Array 3 a -> Array 3 a` (`array.rs`): плоский
//! массив в код без `{Flat a}` не уходит. У массива её видит представление,
//! у семейства - нет (значение семейства указатель при любом поле), и
//! сверяется тип вызываемого. Без этой сверки `Box Int32` в обобщённой
//! функции обрывал прогон «слот спрошен у плоского массива» - измерено.

mod harness;

/// Сколько блоков выдал прогон. Ответ по дороге сверяется с `adamas eval`.
fn allocated(name: &str, source: &str) -> usize {
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    allocated
}

/// Семейство с массивом по параметру.
const BOX: &str = "\
data Box (a : Type) where
  MkBox : Array 4 a -> Box a
";

/// Объявление класса укладки: его имя - соглашение (§4.11).
const FLAT: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout
";

/// Постановка вопроса дословно: `Box Int32` строится и разбирается.
///
/// Блока два - объект `MkBox` и массив; указательный массив взял бы ещё по
/// ячейке на элемент.
#[test]
fn a_flat_array_lives_in_a_family_field() {
    let source = format!(
        "{BOX}
first : Box Int32 -> Int32
first (MkBox xs) = arrayIndex xs 0 Refl

main : Int32
main = first (MkBox (arraySet (arrayNew 4 7) 0 5 Refl))
"
    );
    assert_eq!(allocated("box-flat", &source), 2);
}

/// `Read` значением над плоским массивом - вторая форма постановки.
///
/// За полем стояла вторая стена: тип `let`, которым `arrayRead` переписан,
/// приезжал несведённым редексом решения имплисита и читался указательным.
#[test]
fn a_read_over_a_flat_array_is_returned_by_value() {
    let source = "\
readSecond : (1 xs : Array 4 Int32) -> Read 4 Int32
readSecond xs = arrayRead xs 1 Refl

main : Int32
main = case readSecond (arraySet (arrayNew 4 7) 1 9 Refl) of
  MkRead v ys -> v
";
    allocated("read-by-value", source);
}

/// Обобщённый код с `{Flat a}` видит поле плоским по дескриптору - и до
/// специализации, и после.
#[test]
fn generic_code_with_flat_reads_the_field_by_the_descriptor() {
    let source = format!(
        "{FLAT}{BOX}
again : {{Flat a}} => Box a -> Box a
again (MkBox xs) = MkBox (arraySet xs 0 (arrayIndex xs 1 Refl) Refl)

first : Box Int32 -> Int32
first (MkBox xs) = arrayIndex xs 0 Refl

main : Int32
main = first (again (MkBox (arraySet (arrayNew 4 7) 1 9 Refl)))
"
    );
    allocated("box-generic-flat", &source);
    harness::as_written("box-generic-flat-до", &source)
        .unwrap_or_else(|error| panic!("до специализации: {error}"));
}

/// Без `{Flat a}` поле в обобщённом коде указательное, и плоский массив туда
/// не уходит: отказ при сборке, а не обрыв прогона.
#[test]
fn a_flat_field_does_not_enter_code_without_flat() {
    let source = format!(
        "{BOX}
again : Box a -> Box a
again (MkBox xs) = MkBox (arraySet xs 0 (arrayIndex xs 1 Refl) Refl)

first : Box Int32 -> Int32
first (MkBox xs) = arrayIndex xs 0 Refl

main : Int32
main = first (again (MkBox (arrayNew 4 7)))
"
    );
    let error = harness::compiled(&source).expect_err("плоский массив в код без `Flat`");
    let text = error.to_string();
    assert!(
        text.contains("указательный массив") && text.contains("без `Flat`"),
        "отказ не назвал причину: {text}"
    );
}

/// То же через второе семейство: `W a` держит `Box a`, и `peel : W a -> W a`
/// читает его поле так же указательным.
#[test]
fn the_boundary_holds_through_another_family() {
    let source = format!(
        "{BOX}
data W (a : Type) where
  MkW : Box a -> W a

peel : W a -> W a
peel w = w

open : W Int32 -> Int32
open (MkW (MkBox xs)) = arrayIndex xs 0 Refl

main : Int32
main = open (peel (MkW (MkBox (arrayNew 4 7))))
"
    );
    let error = harness::compiled(&source).expect_err("плоский массив через `W`");
    assert!(error.to_string().contains("без `Flat`"), "{error}");
}

/// Указательный элемент ходит в обобщённый код, как ходил.
#[test]
fn a_pointer_field_still_enters_generic_code() {
    let source = format!(
        "{BOX}
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

again : Box a -> Box a
again (MkBox xs) = MkBox (arraySet xs 0 (arrayIndex xs 1 Refl) Refl)

first : Box Nat -> Nat
first (MkBox xs) = arrayIndex xs 0 Refl

main : Nat
main = first (again (MkBox (arrayNew 4 (Succ Zero))))
"
    );
    allocated("box-pointer", &source);
}

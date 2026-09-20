//! Чего машине стоило второе представление массива (§4.11, трек B волны 2 Фазы 8).
//!
//! Массив у машины теперь плоский блок - байты подряд с адресом
//! (`adamas_core::value::Block`), - а был спайн `arrayNew`/`arraySet`. Обмен
//! здесь не бесплатный в обе стороны, и стенд меряет **обе**:
//!
//! | Точка | Что в ней | Чего ждать |
//! |---|---|---|
//! | `array_new_65536` | `arrayNew` на 65 536 ячеек и одно чтение | спайн заводил узел, блок считает 256 кибибайт: **дороже** |
//! | `column_64_4` | колонка корпуса, 64 ячейки, 4 прохода | запись копирует блок, чтение идёт по смещению |
//! | `column_256_4` | она же, 256 ячеек | отношение двух строк и говорит про класс |
//!
//! Две последние точки берут **программу корпуса**
//! (`tests/golden/eval/workload-column.adamas`), подставляя одну строку
//! размера, - тем же ходом, каким её берёт `adamas-codegen/benches/workloads.rs`.
//! Своя копия программы разъехалась бы с корпусной, и мерился бы не тот код,
//! который проверяется.
//!
//! Что читается отношением `column_256_4 / column_64_4`: **растёт ли выигрыш с
//! длиной**. Спайн читал ячейку поиском от вершины цепочки, то есть платил тем
//! больше, чем длиннее колонка; блок читает по смещению, а платит копией на
//! записи. Снято ли этим слагаемое или множитель, отвечает прогон, а не
//! рассуждение: числа - в `docs/phase8-w2-trackB-notes.md`.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

use std::path::Path;

use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use criterion::{Criterion, criterion_group, criterion_main};

/// Программа корпуса с подставленным размером.
///
/// Подставляется **строка целиком**, и обе подстановки проверяются: молча не
/// сработавшая замена мерила бы колонку из восьми ячеек под именем «256».
fn column(cells: usize, passes: usize) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/eval/workload-column.adamas");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|why| panic!("фикстуры {} нет: {why}", path.display()));
    let sized = source
        .replace("\ncells = 8\n", &format!("\ncells = {cells}\n"))
        .replace("\npasses = 3\n", &format!("\npasses = {passes}\n"));
    assert!(
        sized.contains(&format!("\ncells = {cells}\n"))
            && sized.contains(&format!("\npasses = {passes}\n")),
        "размер в фикстуре написан иначе: подстановка не сработала"
    );
    sized
}

/// Один `arrayNew` и одно чтение: столько стоит **завести** блок.
///
/// Точка нужна отдельно потому, что здесь обмен идёт в **минус**: спайн заводил
/// один узел независимо от длины, блок считает байты. Сколько именно - и
/// говорит эта строка.
fn allocation(cells: usize) -> String {
    format!(
        "\
data Unit where
  MkUnit : Unit

zero : Float32
zero = 0.0

size : UInt64
size = {cells}

main : Float32
main = arrayIndex (arrayNew size zero) 0
"
    )
}

fn prepared(text: &str) -> (Signature, Term) {
    let module = adamas_parser::parse(text).expect("исходник обязан разбираться");
    let (signature, _) =
        adamas_elab::elaborate(&module).expect("исходник обязан проходить проверку");
    let definition = signature.lookup("main").expect("`main` объявлен");
    let body = definition.body.as_ref().expect("у `main` есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    let body = body.substitute_levels(&levels).substitute_rows(&rows);
    (signature, body)
}

fn arrays(criterion: &mut Criterion) {
    let (signature, body) = prepared(&allocation(65536));
    criterion.bench_function("array_new_65536", |bencher| {
        bencher.iter(|| adamas_interp::run(&signature, &body).expect("массив обязан считаться"));
    });

    for cells in [64usize, 256] {
        let (signature, body) = prepared(&column(cells, 4));
        criterion.bench_function(&format!("column_{cells}_4"), |bencher| {
            bencher
                .iter(|| adamas_interp::run(&signature, &body).expect("колонка обязана считаться"));
        });
    }
}

criterion_group!(benches, arrays);
criterion_main!(benches);

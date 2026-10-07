//! Цикл по корпусу - в потоках.
//!
//! nextest параллелит тесты, а не витки внутри теста, и прогон длится столько,
//! сколько самый долгий тест. Самые долгие - циклы по сотне с лишним
//! независимых программ корпуса, и они идут здесь все разом.

#![allow(dead_code, reason = "модуль общий нескольким тестовым крейтам")]

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// `each` над всеми `items` в потоках по числу ядер; ответы - в порядке `items`.
///
/// Паника витка роняет тест тем же текстом, а остальные потоки новых витков
/// не берут. Стек потока - умолчательный, как у потока теста: глубину
/// рекурсии компилятора это не меняет.
pub(crate) fn across<T: Sync, R: Send>(items: &[T], each: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let next = AtomicUsize::new(0);
    let failed = AtomicBool::new(false);
    let workers = std::thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .min(items.len())
        .max(1);
    let mut answers: Vec<Option<R>> = items.iter().map(|_| None).collect();
    std::thread::scope(|scope| {
        let threads: Vec<_> = (0..workers)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    while !failed.load(Ordering::Relaxed) {
                        let index = next.fetch_add(1, Ordering::Relaxed);
                        let Some(item) = items.get(index) else {
                            break;
                        };
                        let guard = Failed(&failed);
                        done.push((index, each(item)));
                        std::mem::forget(guard);
                    }
                    done
                })
            })
            .collect();
        for thread in threads {
            match thread.join() {
                Ok(done) => {
                    for (index, answer) in done {
                        answers[index] = Some(answer);
                    }
                }
                Err(panic) => std::panic::resume_unwind(panic),
            }
        }
    });
    answers.into_iter().flatten().collect()
}

/// Поднимает флаг, если виток раскрутился паникой.
struct Failed<'a>(&'a AtomicBool);

impl Drop for Failed<'_> {
    fn drop(&mut self) {
        self.0.store(true, Ordering::Relaxed);
    }
}

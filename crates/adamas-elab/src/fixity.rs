//! Фикситеты операторов и расстановка скобок в цепочке (§4.4).
//!
//! Разбор оставляет `a + b * c` плоской цепочкой: приоритеты объявляются в
//! программе, и до её чтения таблицы не существует. Здесь она собирается по
//! ходу объявлений и расставляет скобки.
//!
//! **Порядок объявления значим**, как и везде (§4.8): фикситет обязан стоять
//! раньше цепочки, которая его требует. Модульная область видимости Haskell
//! сюда не переносится - она потребовала бы второго прохода по файлу, а
//! ordered scoping заведён ровно затем, чтобы его не было.
//!
//! Результат - вложенные цепочки **по одному оператору**, а не применения:
//! одноместная цепочка есть та форма, которую элаборация умеет с самого
//! начала, и позиция операнда в ней уже решена (§3.3).

use std::collections::HashMap;

use adamas_core::source::Span;
use adamas_parser::ast::{Assoc, Chain, Expr, ExprKind, FixityDecl, Name, Symbol};

use crate::error::ElabError;

/// Объявленные фикситеты.
#[derive(Debug, Default)]
pub struct Fixities(HashMap<Symbol, Fixity>);

/// Приоритет и ассоциативность одного оператора.
#[derive(Clone, Copy, Debug)]
struct Fixity {
    assoc: Assoc,
    precedence: u8,
}

impl Fixities {
    /// Записывает объявление.
    ///
    /// Повтор - отказ: два приоритета у одного оператора означали бы, что
    /// скобки зависят от того, какое объявление прочли.
    ///
    /// # Errors
    ///
    /// Оператор с уже объявленным фикситетом.
    pub fn declare(&mut self, decl: &FixityDecl) -> Result<(), ElabError> {
        for operator in &decl.operators {
            let fixity = Fixity {
                assoc: decl.assoc,
                precedence: decl.precedence,
            };
            if self
                .0
                .insert(Symbol::clone(&operator.text), fixity)
                .is_some()
            {
                return Err(ElabError::Fixity {
                    operator: Symbol::clone(&operator.text),
                    why: "фикситет объявлен дважды",
                    span: operator.span,
                });
            }
        }
        Ok(())
    }

    /// Расставляет скобки в цепочке.
    ///
    /// Цепочка из одного оператора фикситета не требует: расставлять в ней
    /// нечего, и `a + b` пишется до всякого `infixl`.
    ///
    /// # Errors
    ///
    /// Оператор без фикситета либо несводимая ассоциативность.
    pub fn resolve(&self, chain: &Chain, span: Span) -> Result<Expr, ElabError> {
        if chain.tail.len() < 2 {
            return Ok(Expr {
                kind: ExprKind::Chain(chain.clone()),
                span,
            });
        }
        let mut operators = Vec::with_capacity(chain.tail.len());
        for (operator, _) in &chain.tail {
            operators.push((operator.clone(), self.fixity(operator)?));
        }
        let mut climber = Climber {
            chain,
            operators: &operators,
            at: 0,
        };
        let built = climber.climb(0)?;
        debug_assert!(
            climber.at == chain.tail.len(),
            "восхождение обязано израсходовать цепочку целиком"
        );
        Ok(built)
    }

    fn fixity(&self, operator: &Name) -> Result<Fixity, ElabError> {
        self.0
            .get(&operator.text)
            .copied()
            .ok_or_else(|| ElabError::Fixity {
                operator: Symbol::clone(&operator.text),
                why: "фикситет не объявлен, а в цепочке из нескольких операторов \
                      без него не расставить скобок",
                span: operator.span,
            })
    }
}

/// Восхождение по приоритетам.
struct Climber<'a> {
    chain: &'a Chain,
    operators: &'a [(Name, Fixity)],
    /// Сколько операторов уже израсходовано - он же индекс следующего операнда.
    at: usize,
}

impl Climber<'_> {
    /// Операнд по номеру: нулевой - голова цепочки, прочие - за операторами.
    fn operand(&self, index: usize) -> Expr {
        match index.checked_sub(1) {
            None => (*self.chain.head).clone(),
            Some(index) => self.chain.tail[index].1.clone(),
        }
    }

    /// Собирает всё, что связывает не слабее `least`.
    fn climb(&mut self, least: u8) -> Result<Expr, ElabError> {
        let mut left = self.operand(self.at);
        while let Some((operator, fixity)) = self.operators.get(self.at) {
            if fixity.precedence < least {
                break;
            }
            // Цепочка одной силы обязана быть одной ассоциативности, и `infix`
            // не образует её вовсе: где скобки не выводятся, их пишет автор.
            if let Some(previous) = self.at.checked_sub(1) {
                let (before, earlier) = &self.operators[previous];
                if earlier.precedence == fixity.precedence
                    && (earlier.assoc != fixity.assoc || fixity.assoc == Assoc::None)
                {
                    return Err(ElabError::Fixity {
                        operator: Symbol::clone(&operator.text),
                        why: "рядом с оператором той же силы и другой \
                              ассоциативности скобки не выводятся - напишите их",
                        span: before.span.merge(operator.span),
                    });
                }
            }
            self.at += 1;
            // Левая ассоциативность останавливает правую часть на своей силе,
            // правая - пускает её собрать соседа той же.
            let deeper = match fixity.assoc {
                Assoc::Left | Assoc::None => fixity.precedence.saturating_add(1),
                Assoc::Right => fixity.precedence,
            };
            let right = self.climb(deeper)?;
            let span = left.span.merge(right.span);
            left = Expr {
                kind: ExprKind::Chain(Chain {
                    head: Box::new(left),
                    tail: vec![(operator.clone(), right)],
                }),
                span,
            };
        }
        Ok(left)
    }
}

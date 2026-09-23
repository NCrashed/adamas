//! Что компилятор знает про кучу и про ячейку - в тексте, на своих местах
//! (§5.1, §7.2).
//!
//! # Почему `inlayHint`, а не диагностика и не наведение
//!
//! Сервер отвечал на два запроса, и форму третьего выбирают по цене в
//! протоколе и по частоте перерисовки, а не по вкусу.
//!
//! *Диагностика* приходит толчком: сервер шлёт её сам, на каждую правку, целым
//! файлом, и рисуется она в панели проблем. Аллокация проблемой не является -
//! это факт о программе, и на корпусе аллоцирует **1092 определения из 1515 с
//! телом**, то есть подчёркнутым оказалось бы большинство обычного
//! функционального кода. §7.2 просит предупреждать «о ветвях, где reuse
//! структурно возможен, но не применяется **из-за ограничений реализации**», а
//! такой категории у анализа нет вовсе: на корпусе 60 несостоявшихся
//! переиспользований - 45 несовпадений формы, 15 занятых слотов, 0 живых
//! разобранных, - и каждое есть свойство написанного кода, а не нашего
//! бэкенда. Предупреждать о них значило бы называть проблемой правильную
//! программу.
//!
//! *Наведение* спрашивают о точке, и только когда уже подозревают: §5.1 просит
//! ровно обратного - «programmer может explorer'ить без формальных
//! обязательств», то есть видеть статус, не спрашивая.
//!
//! *Подсказка* (`textDocument/inlayHint`) приходит **вытягиванием и по
//! диапазону**: клиент просит ровно то, что видно в окне, и просит заново на
//! правку и на прокрутку. Отвечает она по готовой сигнатуре буфера, второго
//! прохода не делает, и цена её названа числом в
//! `crates/adamas-lsp/tests/protocol.rs`.
//!
//! # Три вида, и все три - показ вердикта, а не обещание машины
//!
//! Формулировки §5.1 - «reuse applies to unique inputs» / «this Node
//! allocation is reused» - говорят о **машине**, а Perceus'а в компиляторе
//! ещё нет: reuse сегодня не выполняется ни разу, и подсказка «ячейка
//! переписана» была бы ложью. Показывается поэтому то, что действительно
//! посчитано: форма кода reuse'у не мешает (`@fbip` принял бы) либо мешает, и
//! вот чем.
//!
//! По той же причине положительная подсказка написана `@noalloc`, а не «не
//! аллоцирует». Это **вердикт**, и область у него у́же машины: установка
//! площадки хендлера стоит трёх блоков кучи, а вердикт про неё молчит (§10
//! вопрос 190). «Атрибут был бы принят» - правда; «не аллоцирует» на таком
//! теле - нет.
//!
//! # Чей это буфер
//!
//! Сигнатура одна на **программу**, а места несут путь модуля
//! ([`adamas_core::sig::Spot`]). Входной файл пути не имеет (§4.8), и
//! `Scope::of` ставится каждому подключённому модулю безусловно
//! (`program.rs`), поэтому `module == None` равносильно «место в этом буфере».
//! Всё прочее сюда не рисуется: спан чужого файла подчеркнул бы случайную
//! строку.

use std::cell::RefCell;
use std::collections::HashMap;

use adamas_core::alloc::{self, Blame, Source};
use adamas_core::sig::{Signature, Spot};
use adamas_core::source::SourceFile;
use adamas_core::term::Name;
use lsp_types::{
    InlayHint, InlayHintLabel, InlayHintLabelPart, InlayHintLabelPartTooltip, InlayHintTooltip,
    Location, MarkupContent, MarkupKind, Position, Range, Uri,
};

use crate::position::{self, Encoding};
use crate::{Document, project};

/// Что сказано над определением, которое не аллоцирует.
const NOALLOC: &str = "@noalloc";

/// Пояснение к положительному вердикту.
///
/// Названа именно область вердикта: §10 вопрос 190 измерил, что установка
/// площадки хендлера стоит трёх блоков кучи и в перечень источников §5.1 не
/// входит. Подсказка, обещавшая бы «ноль аллокаций», разносила бы этот пробел
/// по всем окнам сразу.
const NOALLOC_WHY: &str = "`@noalloc` на этом определении был бы принят: среди источников, \
                           перечисленных §5.1, вердикт не нашёл ни одного. Вердикт отвечает про \
                           перечисленное - установка площадки хендлера в перечень не входит и \
                           стоит трёх блоков кучи (§10 вопрос 190).";

/// Пояснение к переписанной ячейке.
const REUSE_WHY: &str = "Построение занимает слот ячейки, разобранной ветвью: форма кода reuse'у \
                         не мешает, и на уникальном входе (RC = 1) оно перепишет слоты вместо \
                         аллокации (§5.1). Уникальность есть свойство места вызова, и проверка её \
                         не обещает; Perceus в компиляторе пока не реализован, поэтому сегодня \
                         это утверждение о форме кода, а не о машине.";

/// Пояснение к звену цепочки, у которого места нет.
const NO_SPOT: &str = "Места нет: за этим именем стоит запись, собранная элаборацией - значение \
                       модуля либо словарь инстанса, - и написанного выражения автор не писал. \
                       Указать было бы некуда (82 таких определения на корпусе).";

/// Подсказки для видимого куска буфера.
///
/// `range` - окно клиента; за его пределы подсказки не считаются, и это не
/// экономия, а требование протокола: клиент рисует то, что попросил.
#[must_use]
pub fn hints(uri: &Uri, document: &Document, range: Range, encoding: Encoding) -> Vec<InlayHint> {
    let Some(signature) = document.signature() else {
        return Vec::new();
    };
    let file = SourceFile::new(uri.as_str(), document.text());
    // Окно, которое не переводится, прижимается к границам файла, а не гасит
    // ответ: клиент вправе назвать строку за концом буфера - текст он видит с
    // задержкой, - и молчание в ответ читалось бы «подсказок здесь нет».
    let from = position::offset(&file, range.start, encoding).unwrap_or(0);
    let upto =
        position::offset(&file, range.end, encoding).unwrap_or_else(|| document.text().len());
    let shown = Shown {
        uri,
        document,
        signature,
        file: &file,
        encoding,
        window: from..upto,
        borrowed: RefCell::new(HashMap::new()),
    };
    let mut found = Vec::new();
    shown.status(&mut found);
    shown.places(&mut found);
    // Порядок в ответе клиенту безразличен, а в прогоне - нет: имена приходят
    // из хеш-таблицы сигнатуры.
    found.sort_by_key(|hint| (hint.position.line, hint.position.character));
    found
}

/// Общее для всех подсказок одного запроса.
struct Shown<'a> {
    uri: &'a Uri,
    document: &'a Document,
    signature: &'a Signature,
    file: &'a SourceFile,
    encoding: Encoding,
    window: std::ops::Range<usize>,
    /// Тексты подключённых модулей, уже прочитанные в этом запросе.
    ///
    /// Кэш нужен не ради диска, а ради [`SourceFile`]: он строит таблицу начал
    /// строк, то есть проходит текст целиком, а звенья цепочек спрашивают место
    /// десятками. Измерено стендом `what_a_hint_costs`: капстоун целиком стоил
    /// **3798 мкс** до кэша и **1598** после. `None` в записи - модуль, чей файл
    /// прочитать не вышло: второй попытки он не получает.
    borrowed: RefCell<HashMap<String, Option<(Uri, SourceFile)>>>,
}

impl Shown<'_> {
    /// Видно ли смещение в окне клиента.
    fn visible(&self, offset: usize) -> bool {
        self.window.contains(&offset)
    }

    /// Позиция подсказки по байтовому смещению.
    fn at(&self, offset: usize) -> Option<Position> {
        position::position(self.file, offset, self.encoding)
    }

    /// Статус над каждым определением, **написанным в этом буфере**.
    ///
    /// Место берётся у дерева, а не у [`Signature::origin`]: таблица позиций
    /// файла не несёт, а сигнатура одна на программу, и место имени из
    /// подключённого модуля нарисовалось бы по чужому тексту.
    fn status(&self, out: &mut Vec<InlayHint>) {
        let Some(module) = self.document.module() else {
            return;
        };
        for (name, span) in adamas_elab::cursor::definitions(self.signature, module) {
            if !self.visible(span.start()) {
                continue;
            }
            let Some(position) = self.at(span.start()) else {
                continue;
            };
            let blamed = alloc::blame(self.signature, &name);
            let (mut label, mut why) = match &blamed {
                Some(blame) => (
                    self.chain(&name, blame),
                    format!("Аллоцирует в куче Perceus: {blame}."),
                ),
                None => (vec![part(NOALLOC)], NOALLOC_WHY.to_owned()),
            };
            if let Some(reuse) = self.signature.reuse(&name) {
                let (text, said) = match (&reuse.blocked, reuse.rewrites.len()) {
                    (Some(blocked), _) => (
                        ", reuse не сошёлся".to_owned(),
                        format!("Переиспользование ячейки: {}.", blocked.fault),
                    ),
                    (None, count) => (
                        format!(", reuse {count}"),
                        format!(
                            "Построений, занимающих слот разобранной ячейки: {count}. {REUSE_WHY}"
                        ),
                    ),
                };
                label.push(part(&text));
                why.push_str("\n\n");
                why.push_str(&said);
            }
            out.push(InlayHint {
                position,
                label: InlayHintLabel::LabelParts(label),
                kind: None,
                text_edits: None,
                tooltip: Some(InlayHintTooltip::MarkupContent(MarkupContent {
                    kind: MarkupKind::PlainText,
                    value: why,
                })),
                padding_left: None,
                padding_right: Some(true),
                data: None,
            });
        }
    }

    /// Цепочка вины в подписи подсказки.
    ///
    /// Цепочку, а не вердикт: «`f` аллоцирует» не говорит, что чинить, а
    /// `blame` знает путь до места целиком. Каждое звено - своя часть подписи со
    /// **своим** местом, то есть щелчком: клиент ведёт по `location` части.
    fn chain(&self, name: &Name, blame: &Blame) -> Vec<InlayHintLabelPart> {
        // Первое звено - само определение: щелчок по слову `куча` ведёт туда,
        // где оно аллоцирует. Без этого читателю пришлось бы искать место
        // глазами в собственном теле.
        let mut label = vec![InlayHintLabelPart {
            value: "куча".to_owned(),
            location: self
                .signature
                .allocated_at(name)
                .and_then(|spot| self.located(spot)),
            ..InlayHintLabelPart::default()
        }];
        label.push(part(": "));
        for link in blame.through() {
            label.push(self.link(link));
            label.push(part(" → "));
        }
        label.push(part(&shortly(blame.source())));
        label
    }

    /// Звено цепочки: имя со своим местом, либо имя, у которого места нет.
    ///
    /// Второй случай не выдумка и не редкость: в цепочку попадает `Source::Call`
    /// определения **с телом**, а значение модуля и словарь инстанса тело имеют,
    /// написанного выражения - нет. Молчать о нём нельзя: читатель принял бы
    /// неработающий щелчок за поломку редактора, а не за границу анализа.
    /// Поэтому такое звено берётся в угловые кавычки и объясняется подсказкой
    /// части.
    fn link(&self, link: &Name) -> InlayHintLabelPart {
        match self
            .signature
            .allocated_at(link)
            .and_then(|spot| self.located(spot))
        {
            Some(location) => InlayHintLabelPart {
                value: link.to_string(),
                location: Some(location),
                ..InlayHintLabelPart::default()
            },
            None => InlayHintLabelPart {
                value: format!("‹{link}›"),
                tooltip: Some(InlayHintLabelPartTooltip::String(NO_SPOT.to_owned())),
                ..InlayHintLabelPart::default()
            },
        }
    }

    /// Место в адрес протокола - хоть в этом файле, хоть в подключённом.
    ///
    /// Путь модуля в файл переводит буфер по прошлому проходу
    /// ([`Document::file_of`]); модуля нет - место принадлежит самому буферу.
    fn located(&self, spot: &Spot) -> Option<Location> {
        let Some(module) = spot.module.as_deref() else {
            return Some(Location {
                range: position::range(self.file, spot.span, self.encoding),
                uri: self.uri.clone(),
            });
        };
        let mut borrowed = self.borrowed.borrow_mut();
        let known = borrowed.entry(module.to_owned()).or_insert_with(|| {
            let path = self.document.file_of(module)?;
            let uri = project::uri_of(path)?;
            let text = std::fs::read_to_string(path).ok()?;
            let file = SourceFile::new(uri.as_str(), text);
            Some((uri, file))
        });
        let (uri, file) = known.as_ref()?;
        Some(Location {
            range: position::range(file, spot.span, self.encoding),
            uri: uri.clone(),
        })
    }

    /// Места внутри тел: где аллоцирует и что делает с разобранной ячейкой.
    ///
    /// Идут по **сигнатуре**, а не по дереву, и это не небрежность: место
    /// принадлежит выражению, у которого имени нет, а `module == None` уже
    /// значит «в этом буфере». Так подсказку получает и член инстанса, чьё имя
    /// (`Functor#List.map`) в тексте не написано вовсе.
    fn places(&self, out: &mut Vec<InlayHint>) {
        for name in self.signature.names() {
            // Окно спрашивается **до** цепочки вины: собрать её ради подсказки,
            // которую тут же выбросят, значит платить обходом графа вызовов за
            // каждую прокрутку.
            if let Some(spot) = self
                .signature
                .allocated_at(&name)
                .filter(|it| self.here(it))
            {
                let why = alloc::blame(self.signature, &name)
                    .map_or_else(String::new, |blame| format!("Аллоцирует: {blame}."));
                self.mark(out, spot, "куча", &why);
            }
            let Some(reuse) = self.signature.reuse(&name) else {
                continue;
            };
            for spot in &reuse.rewrites {
                self.mark(out, spot, "reuse", REUSE_WHY);
            }
            if let Some(blocked) = &reuse.blocked {
                self.mark(
                    out,
                    &blocked.spot,
                    "без reuse",
                    &format!("{}.", blocked.fault),
                );
            }
        }
    }

    /// В этом ли буфере место и видно ли оно в окне.
    ///
    /// Первая половина - не оптимизация: сигнатура одна на программу, и спан
    /// чужого файла, нарисованный по этому тексту, подчеркнул бы случайную
    /// строку.
    fn here(&self, spot: &Spot) -> bool {
        spot.module.is_none() && self.visible(spot.span.start())
    }

    /// Одна подсказка у места - если место в этом буфере и видно в окне.
    fn mark(&self, out: &mut Vec<InlayHint>, spot: &Spot, label: &str, why: &str) {
        if !self.here(spot) {
            return;
        }
        let Some(position) = self.at(spot.span.start()) else {
            return;
        };
        out.push(InlayHint {
            position,
            label: InlayHintLabel::String(label.to_owned()),
            kind: None,
            text_edits: None,
            tooltip: (!why.is_empty()).then(|| {
                InlayHintTooltip::MarkupContent(MarkupContent {
                    kind: MarkupKind::PlainText,
                    value: why.to_owned(),
                })
            }),
            padding_left: None,
            padding_right: Some(true),
            data: None,
        });
    }
}

/// Часть подписи без места и без пояснения.
fn part(value: &str) -> InlayHintLabelPart {
    InlayHintLabelPart {
        value: value.to_owned(),
        ..InlayHintLabelPart::default()
    }
}

/// Конец цепочки одним словом.
///
/// Полное предложение про каждый источник уже написано - его печатает
/// [`Blame`], и в подсказке оно стоит пояснением. Подпись же рисуется в строке
/// кода, и второй копии текста здесь нет: только имя того, что аллоцирует.
fn shortly(source: &Source) -> String {
    match source {
        Source::Construct(name) | Source::Call(name) => name.to_string(),
        Source::Record => "запись".to_owned(),
        Source::Closure => "замыкание".to_owned(),
        Source::Partial(name) => format!("{name} частично"),
        Source::Operation(name) => format!("операция {name}"),
        Source::Resumption { effect, .. } => format!("хендлер {effect}"),
        Source::Boxing => "боксирование".to_owned(),
        Source::Opaque(name) => format!("{name} без тела"),
    }
}

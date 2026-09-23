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
//! allocation is reused» - говорят о **машине**, и подсказка обещать этого не
//! может. Не потому, что механизма нет: оба понижения вставляют `adamas_reuse`
//! (`codegen::perceus`, с 2026-09-09), и в порождённом C он виден. Потому, что
//! срабатывание **динамическое** - решает счётчик ссылок в точке разбора, - а
//! подсказка статична и про конкретный прогон не знает ничего. «Ячейка
//! переписана» было бы обещанием за рантайм.
//!
//! Показывается поэтому посчитанное: форма кода reuse'у не мешает (`@fbip`
//! принял бы) либо мешает, и вот чем. У машины (`adamas eval`) reuse нет вовсе,
//! и не нужен: дерево-обходчику переписывать нечего.
//!
//! По той же причине положительная подсказка написана `@noalloc`, а не «не
//! аллоцирует». Это **вердикт**, и область у него у́же машины: установка
//! площадки хендлера стоит трёх блоков кучи, а вердикт про неё молчит (§10
//! вопрос 190). «Атрибут был бы принят» - правда; «не аллоцирует» на таком
//! теле - нет.
//!
//! # Чего здесь нет: подсветка области региона
//!
//! §7.2 просит ещё одну возможность - «при работе с `Ref r a` визуализировать
//! scope региона `r`, где ссылка валидна», - и она **не сделана нарочно**:
//! компилятор не знает, что такое `Ref r a`.
//!
//! Это не догадка, а его собственные слова: заголовок
//! [`adamas_core::prim::RegionOp`] говорит прямо - «регион здесь
//! **представление**, а не типовая сторона: `Alloc r`, `Ref r a` и
//! `withRegion` объявляются **программой** и стоят на эффектах». Примитивы
//! ниже них есть (`regionNew`, `regionRead`, …), но к написанному `Ref r Nat`
//! они отношения не имеют.
//!
//! Обе приметы, по которым регион можно было бы узнать, промахиваются, и
//! промах измерен на корпусе.
//!
//! *По имени.* Метку называют `Region` в шести файлах и `Reg` в двух
//! (`signature-effect-parameterized`, `row-solution-captures-a-local`).
//! Различие это законно - имя объявляет программа, - и всякий, кто напишет
//! `Zone`, останется без подсветки.
//!
//! *По форме.* «Семейство со стёртым первым параметром» ловит **не регионы**:
//! на корпусе таких восемь, и один из них - `Vect : (0 n : Nat) -> Type ->
//! Type`, длина вектора. «Эффект со стёртым параметром» - четырнадцать, и
//! среди них `Src (0 a : Type)` и `St (0 a : Type)`, к регионам не относящиеся
//! вовсе.
//!
//! Подсветить **область связывания** `r` компилятор, конечно, может - это
//! обычная лексическая область, - но назвать это «областью региона» значило бы
//! изобразить анализ, которого нет: тот же ответ он дал бы `Vect` и `Src`.
//! Гарантия §3.6 стоит не на распознавании региона, а на двух общих
//! механизмах - связывание метки в домене и запечатывание погашения (§4.8), -
//! и подсветке отвечать нечем.
//!
//! Тот же жанр, что у предупреждения о ветвях без reuse (волна 3): §7.2 просит
//! показать категорию, которой у компилятора нет.
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
use std::collections::{BTreeMap, HashMap};

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
                         аллокации (§5.1). Вставку делают оба понижения; сработает она или нет, \
                         решает счётчик ссылок в рантайме, а уникальность есть свойство места \
                         вызова - поэтому подсказка говорит о форме кода, а не о конкретном \
                         прогоне. У машины (`adamas eval`) reuse нет вовсе.";

/// Пояснение к связыванию, которое закрывает не оно само.
const SPENT: &str = "Связывание линейно по построению (§3.3), но деструктора здесь не будет: \
                     значение расходуется дальше, и закроет его тот, кто взял. У `unique data` \
                     деструктора нет вовсе - память освобождается статически.";

/// Пояснение к месту вставки деструктора.
const RELEASED: &str = "Сюда компилятор вставит вызов деструктора - на выходе из области \
                        видимости связывания, и на **всех** выходах: включая тот, где \
                        вычисление оборвано эффектом (§3.3 × §3.4). Порядок между несколькими \
                        - LIFO: связанное позже закрывается раньше.";

/// Пояснение к метке, которую снимает хендлер.
const DISCHARGES: &str = "Метку `handle` берёт из первой ветки-операции, если она не написана за \
                          `@` (§4.1): в тексте её тут нет, а снимается именно она. На корпусе так \
                          написаны 151 хендлер из 175.";

/// Пояснение к использованию операции.
const PERFORMS: &str = "Хендлеры **этого файла**, гасящие метку операции. Какой из них сработает, \
                        решает место вызова, а не место операции: `handle` берёт названное \
                        вычисление (§3.4), поэтому операция и её хендлер стоят в разных телах. \
                        «в ряд» - в этом файле метка не гасится и уходит наверх по ряду.";

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
    shown.resources(&mut found);
    shown.effects(&mut found);
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

    /// Жизнь ресурса: где взят и где компилятор вставит деструктор (§3.3, §7.2).
    ///
    /// Два места на связывание, и оба нужны. §7.2 просит эту пару затем, чтобы
    /// «понимать exceptional-exit cleanup поведение»: вставка стоит на **всех**
    /// выходах из области видимости, включая тот, где вычисление оборвано
    /// эффектом, и увидеть это по тексту нечем - в тексте вызова деструктора
    /// нет.
    ///
    /// Показывается **посчитанное**, а не правило: отвечает
    /// [`adamas_elab::lifecycle`], который заполняется в той самой точке, где
    /// решение принято. Повторить правило здесь значило бы завести вторую его
    /// запись, и подсказка начала бы врать ровно тогда, когда правило изменят.
    fn resources(&self, out: &mut Vec<InlayHint>) {
        let found = &self.document.observed().lifecycles;
        for it in found.iter() {
            if !self.visible(it.acquired.start()) {
                continue;
            }
            let Some(position) = self.at(it.acquired.start()) else {
                continue;
            };
            let (label, why) = match &it.released {
                Some(released) => (
                    it.owned.keyword().to_owned(),
                    format!(
                        "Связывание линейно по построению (§3.3). Компилятор вставит \
                         `{} {}` на выходе из области видимости - на всех выходах, \
                         включая обрыв эффектом.",
                        released.drop, it.name
                    ),
                ),
                None => (
                    format!("{}, расходуется", it.owned.keyword()),
                    SPENT.to_owned(),
                ),
            };
            out.push(InlayHint {
                position,
                label: InlayHintLabel::LabelParts(vec![part(&label)]),
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
        // Место вставки одно на всю группу, а деструкторов там бывает
        // несколько, и порядок между ними наблюдаем: §3.3 обещает LIFO, и
        // корпус (`eval/resource.adamas`) различает `[1, 8, 9]` от `[1, 9, 8]`.
        // Значит и подсказка обязана показать их в том же порядке - иначе она
        // говорит про порядок неправду.
        let mut grouped: BTreeMap<usize, Vec<String>> = BTreeMap::new();
        for it in found.iter() {
            let Some(released) = it.released.as_ref() else {
                continue;
            };
            grouped
                .entry(released.at.end())
                .or_default()
                .insert(0, format!("{} {}", released.drop, it.name));
        }
        for (at, calls) in grouped {
            if !self.visible(at) {
                continue;
            }
            let Some(position) = self.at(at) else {
                continue;
            };
            out.push(InlayHint {
                position,
                label: InlayHintLabel::LabelParts(vec![part(&calls.join(", "))]),
                kind: None,
                text_edits: None,
                tooltip: Some(InlayHintTooltip::MarkupContent(MarkupContent {
                    kind: MarkupKind::PlainText,
                    value: RELEASED.to_owned(),
                })),
                padding_left: Some(true),
                padding_right: None,
                data: None,
            });
        }
    }

    /// Погашение эффекта: какую метку снимает `handle` и кто снимает эту
    /// (§3.4, §7.2).
    ///
    /// Два места, и оба показывают **посчитанное**, а не пересказ текста.
    ///
    /// У `handle` метка чаще не написана вовсе: он берёт её из первой ветки, и
    /// на корпусе так написаны 151 хендлер из 175. `handle counter with …` не
    /// называет `State` нигде, и узнать её читателю сегодня нечем.
    ///
    /// У использования операции названы хендлеры **этого файла**, гасящие её
    /// метку, - каждый своим именем и своим адресом, то есть щелчком. Это и
    /// есть disambiguation, которого просит §7.2: в `eval/state.adamas` метку
    /// `State` гасят четыре разных хендлера, и один `get` вправе попасть в
    /// любой из них.
    ///
    /// **Названная граница, и она свойство языка, а не пробел анализа.**
    /// «Хендлер в области видимости» точного ответа не имеет: `handle` берёт
    /// **названное** вычисление (§3.4), поэтому операция и её хендлер стоят в
    /// разных телах почти всегда, а какой из них сработает - свойство места
    /// вызова, а не места операции. Показывается поэтому **множество**
    /// кандидатов, и подсказка говорит об этом словами; хендлеры в других
    /// файлах в него не входят.
    fn effects(&self, out: &mut Vec<InlayHint>) {
        let handlers = &self.document.observed().handlers;
        for it in handlers.sites() {
            if !self.visible(it.at.start()) {
                continue;
            }
            let Some(position) = self.at(it.at.start()) else {
                continue;
            };
            out.push(InlayHint {
                position,
                label: InlayHintLabel::LabelParts(vec![part(&shortly_named(&it.effect))]),
                kind: None,
                text_edits: None,
                tooltip: Some(InlayHintTooltip::MarkupContent(MarkupContent {
                    kind: MarkupKind::PlainText,
                    value: DISCHARGES.to_owned(),
                })),
                padding_left: None,
                padding_right: Some(true),
                data: None,
            });
        }
        for it in handlers.used() {
            if !self.visible(it.at.start()) {
                continue;
            }
            let Some(position) = self.at(it.at.start()) else {
                continue;
            };
            let mut label = vec![part(&format!("{}: ", shortly_named(&it.effect)))];
            let mut first = true;
            for site in handlers.discharging(&it.effect) {
                if !first {
                    label.push(part(", "));
                }
                first = false;
                label.push(InlayHintLabelPart {
                    value: shortly_named(&site.owner),
                    location: Some(Location {
                        range: position::range(self.file, site.at, self.encoding),
                        uri: self.uri.clone(),
                    }),
                    ..InlayHintLabelPart::default()
                });
            }
            // Молчать о пустом множестве нельзя: читатель принял бы отсутствие
            // подсказки за отсутствие механизма, а не за отсутствие хендлера.
            if first {
                label.push(part("в ряд"));
            }
            out.push(InlayHint {
                position,
                label: InlayHintLabel::LabelParts(label),
                kind: None,
                text_edits: None,
                tooltip: Some(InlayHintTooltip::MarkupContent(MarkupContent {
                    kind: MarkupKind::PlainText,
                    value: PERFORMS.to_owned(),
                })),
                padding_left: None,
                padding_right: Some(true),
                data: None,
            });
        }
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
/// Имя без квалификации модулем: подсказка стоит **в том файле**, где написано
/// использование, и путь в ней занимал бы место, ничего не добавляя.
fn shortly_named(name: &str) -> String {
    name.rsplit('.').next().unwrap_or(name).to_owned()
}

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

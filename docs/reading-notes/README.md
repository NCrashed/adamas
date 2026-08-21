# Reading notes

Конспекты статей, на которые опирается дизайн. Полный список источников —
`adamas-design.md` §11.

Формат файла: `<год>-<первый-автор>-<короткое-название>.md`, например
`2018-atkey-qtt.md`. Внутри — что решает статья, какие именно решения из
`adamas-design.md` на неё опираются, и где наш дизайн отходит от оригинала и
почему. Пересказ ради пересказа не нужен: конспект пишется, чтобы через год
можно было вспомнить, почему сделано так.

## Приоритетное чтение перед Фазой 1

§9 Фазы 0 требует прочитать как минимум эти пять до старта работы над ядром:

- [ ] Atkey, R. (2018). *Syntax and Semantics of Quantitative Type Theory.* LICS.
      Основание §3.2 — кратности как semiring, erasure на уровне теории.
- [ ] Brady, E. (2021). *Idris 2: Quantitative Type Theory in Practice.* ECOOP.
      Как QTT выглядит в реальном компиляторе; ближайший референс для §3.2–3.3.
- [ ] Reinking, A., Xie, N., de Moura, L., Leijen, D. (2021). *Perceus: Garbage
      Free Reference Counting with Reuse.* PLDI. Основание §5.1, включая FBIP.
- [ ] Xie, N. et al. (2020). *Effect Handlers, Evidently.* ICFP.
      Evidence translation — механика §3.4.
- [ ] Swamy, N. et al. (2016). *Dependent Types and Multi-Monadic Effects in
      F\*.* POPL. Ориентир для §3.7 (верификация).

## Acceptance criterion

Фаза 0 закрывается, когда все пять отмечены и конспекты лежат здесь
(`adamas-design.md` §9, «Ключевые статьи прочитаны, конспекты в репозитории»).

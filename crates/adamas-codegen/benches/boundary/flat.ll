; Уклад (в): плоское слово. Чужой указатель `adamas_value` не становится.
;
; Пишется диалектом текстового эмиттера (`crates/adamas-codegen/src/emit_llvm.rs`)
; и его консервативным подмножеством: ни `target datalayout`, ни `target
; triple`, у арифметики нет `nsw`/`nuw`, у `getelementptr` нет ни `inbounds`,
; ни `nuw`. Правило проверяется прогоном на минимальной поддерживаемой версии
; (`llvm::MINIMUM_MAJOR`), а не чтением.
;
; Пара `ptrtoint`/`inttoptr` здесь - ровно та же, которой эмиттер сегодня
; проводит плоское значение через границу кадра (`Builder::into_word` и
; `Builder::from_word`). Ни одной формы сверх уже печатаемых уклад не просит.

declare ptr @adamas_probe_open(i64)
declare i64 @adamas_probe_step(ptr, i64)
declare i64 @adamas_probe_calls(ptr)
declare void @adamas_probe_close(ptr)

define i64 @adamas_entry(i64 %calls) {
entry:
  %handle = call ptr @adamas_probe_open(i64 2654435761)
  %bits = ptrtoint ptr %handle to i64
  br label %head

head:
  %i = phi i64 [ 0, %entry ], [ %next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %mixed, %body ]
  %more = icmp ult i64 %i, %calls
  br i1 %more, label %body, label %done

body:
  %back = inttoptr i64 %bits to ptr
  %got = call i64 @adamas_probe_step(ptr %back, i64 %i)
  %mixed = xor i64 %acc, %got
  %next = add i64 %i, 1
  br label %head

done:
  %made = call i64 @adamas_probe_calls(ptr %handle)
  %answer = xor i64 %acc, %made
  call void @adamas_probe_close(ptr %handle)
  ret i64 %answer
}

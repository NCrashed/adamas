; Уклад (а): однополевой объект под RC, деструктор пуст.
;
; Слот читается и пишется **инструкцией**, а не вызовом `adamas_field` /
; `adamas_set_field`, - тем же правилом, каким это делает эмиттер
; (`crates/adamas-codegen/src/emit_llvm.rs`, «Что объектный слой знает о
; раскладке»): смещение слота есть `HEADER_BYTES + slot * SLOT_BYTES`, то есть
; 8 у нулевого. `getelementptr i8` без `inbounds` и без `nuw` - консервативное
; подмножество.
;
; `ptr null` вторым аргументом `@adamas_drop` и есть «деструктор пуст»: обход
; детей по этому слоту читал бы заголовок по чужому адресу.
;
; Тег `65527` (0xFFF7) - первое свободное под занятыми рантаймом; в `adamas.h`
; он не вносится, см. `entry.c`.

declare ptr @adamas_alloc(i16, i64)
declare void @adamas_drop(ptr, ptr)

declare ptr @adamas_probe_open(i64)
declare i64 @adamas_probe_step(ptr, i64)
declare i64 @adamas_probe_calls(ptr)
declare void @adamas_probe_close(ptr)

define i64 @adamas_entry(i64 %calls) {
entry:
  %handle = call ptr @adamas_probe_open(i64 2654435761)
  br label %head

head:
  %i = phi i64 [ 0, %entry ], [ %next, %body ]
  %acc = phi i64 [ 0, %entry ], [ %mixed, %body ]
  %more = icmp ult i64 %i, %calls
  br i1 %more, label %body, label %done

body:
  %box = call ptr @adamas_alloc(i16 65527, i64 1)
  %slot = getelementptr i8, ptr %box, i64 8
  store ptr %handle, ptr %slot
  %back = load ptr, ptr %slot
  %got = call i64 @adamas_probe_step(ptr %back, i64 %i)
  call void @adamas_drop(ptr %box, ptr null)
  %mixed = xor i64 %acc, %got
  %next = add i64 %i, 1
  br label %head

done:
  %made = call i64 @adamas_probe_calls(ptr %handle)
  %answer = xor i64 %acc, %made
  call void @adamas_probe_close(ptr %handle)
  ret i64 %answer
}

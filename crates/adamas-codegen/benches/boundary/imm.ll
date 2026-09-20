; Уклад (б): сдвинутое непосредственное `(p << 1) | 1`.
;
; Арифметика печатается **строками**, а не вызовом `@adamas_imm`, и это не
; вольность стенда. Сегодняшний эмиттер непосредственное строит одним способом -
; вызовом `@adamas_con0(i16)` с тегом, известным на сборке
; (`crates/adamas-codegen/src/emit_llvm.rs`); непосредственного из значения,
; посчитанного в рантайме, он не строит нигде. Значит уклад (б) - это либо
; новая точка входа рантайма в блоке `declare`, либо вот эти четыре строки; что
; из двух дешевле, спрашивать незачем, а печатать всё равно придётся новое.
;
; Консервативное подмножество: ни `nsw`, ни `nuw` у сдвига; `ashr`, а не `lshr`,
; потому что `adamas_imm_get` в рантайме есть знаковый сдвиг вправо
; (`crates/adamas-runtime/c/object.c`).

declare void @adamas_drop(ptr, ptr)

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
  %shifted = shl i64 %bits, 1
  %tagged = or i64 %shifted, 1
  %value = inttoptr i64 %tagged to ptr
  %raw = ptrtoint ptr %value to i64
  %plain = ashr i64 %raw, 1
  %back = inttoptr i64 %plain to ptr
  %got = call i64 @adamas_probe_step(ptr %back, i64 %i)
  call void @adamas_drop(ptr %value, ptr null)
  %mixed = xor i64 %acc, %got
  %next = add i64 %i, 1
  br label %head

done:
  %made = call i64 @adamas_probe_calls(ptr %handle)
  %answer = xor i64 %acc, %made
  call void @adamas_probe_close(ptr %handle)
  ret i64 %answer
}

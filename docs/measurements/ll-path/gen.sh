#!/usr/bin/env bash
# Синтетический C, по форме близкий к выходу наивного кодогенератора Adamas
# после мономорфизации: много мелких функций, RC вокруг указателей,
# конструкторы как структуры со счётчиком.
n=$1
cat <<'HDR'
#include <stdlib.h>
typedef struct Obj { long rc; long tag; struct Obj *a; struct Obj *b; } Obj;
static inline Obj* dup(Obj *o){ if(o) o->rc++; return o; }
static void drop(Obj *o){ if(o && --o->rc==0){ drop(o->a); drop(o->b); free(o); } }
static Obj* mk(long t, Obj *a, Obj *b){ Obj *o=malloc(sizeof(Obj)); o->rc=1; o->tag=t; o->a=a; o->b=b; return o; }
HDR
for ((i = 0; i < n; i++)); do echo "Obj* f$i(Obj *x, long k);"; done
for ((i = 0; i < n; i++)); do
  j=$(( (i + 1) % n ))
  cat <<EOF
Obj* f$i(Obj *x, long k) {
  if (!x) return mk($i, 0, 0);
  Obj *l = dup(x->a);
  Obj *r = dup(x->b);
  long t = x->tag + k;
  Obj *s = (k > 0) ? f$j(l, k - 1) : l;
  Obj *u = mk(t, s, r);
  drop(x);
  return u;
}
EOF
done
cat <<'FTR'
int main(void) {
  Obj *o = mk(0,0,0);
  for (long i = 0; i < 10; i++) o = f0(o, 3);
  long acc = o->tag; drop(o); return (int)(acc & 1);
}
FTR

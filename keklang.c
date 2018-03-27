#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <errno.h>
#include <math.h>
#include "mpc.h"

static char input[2084];
struct kval;
struct kenv;
typedef struct kval kval;
typedef struct kenv kenv;
static int exit_main = -1;

mpc_parser_t* Number;
mpc_parser_t* Double;
mpc_parser_t* Symbol;
mpc_parser_t* String;
mpc_parser_t* Comment;
mpc_parser_t* Sexpr;
mpc_parser_t* Qexpr;
mpc_parser_t* Expr;  
mpc_parser_t* Kek; 

typedef kval*(*kbuiltin)(kenv*, kval*);

#define KDELWHENFALSE(args, cond, fmt, ...) \
  if (!(cond)) { \
    kval *err = kval_err(fmt, ##__VA_ARGS__); \
    kval_del(args); return err;\
  }
#define KDELWHENFALSE_TYPE(func, args, index, expect) \
  KDELWHENFALSE(args, args->cell[index]->type == expect, \
    "Function '%s' recieved incorrect type for the arg %i. Got '%s' but expected '%s'.", \
    func, index, ktype_name(args->cell[index]->type), ktype_name(expect));
#define KDELWHENFALSE_NUM(func, args, num) \
  KDELWHENFALSE(args, args->count == num, \
    "Function '%s' recieved incorrect number of args. Got %i but expected %i.", \
    func, args->count, num);
#define KDELWHENFALSE_NOT_EMPTY(func, args, index) \
  KDELWHENFALSE(args, args->cell[index]->count != 0, \
    "Function '%s' recieved {} for arg %i.", func, index);

struct kval {
  int type;
  double num;
  char *err;
  char *sym;
  char *str;

  kbuiltin builtin;
  kenv *env;
  kval *formals;
  kval *body;

  int count;
  struct kval **cell;
};

struct kenv {
  kenv *par;
  int count;
  char **syms;
  kval **vals;
};

enum {KVAL_ERR, KVAL_OK, KVAL_NUM, KVAL_SYM, KVAL_STR ,KVAL_SEXPR, KVAL_QEXPR, KVAL_FUNC};

char* ktype_name(int t) {
  switch(t) {
    case KVAL_FUNC: return "Function";
    case KVAL_ERR: return "Error";
    case KVAL_NUM: return "Number";
    case KVAL_SYM: return "Symbol";
    case KVAL_SEXPR: return "Expression";
    case KVAL_QEXPR: return "Quoted Expression";
    case KVAL_STR: return "String";
    default: return "Unknown";
  }
}

kval *kval_num(double x) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_NUM;
  v->num = x;
  return v;
}

kval *kval_err(char* fmt, ...) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_ERR;

  va_list va;
  va_start(va, fmt);

  v->err = malloc(512);
  vsnprintf(v->err, 511, fmt, va);
  v->err = realloc(v->err, strlen(v->err) + 1);
  va_end(va);
  
  return v;
}

kval *kval_ok(void) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_OK;
  v->count = 0;
  v->cell = NULL;
  return v;
}

kval *kval_sym(char* s) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_SYM;
  v->sym = malloc(strlen(s) + 1);
  strcpy(v->sym, s);
  return v;
}

kval *kval_sexpr(void) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_SEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

kval *kval_qexpr(void) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_QEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

kval *kval_func(kbuiltin function) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_FUNC;
  v->builtin = function;
  return v;
}

kval *kval_str(char *s) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_STR;
  v->str = malloc(strlen(s) + 1);
  strcpy(v->str, s);
  return v;
}

kenv *kenv_new(void);
void kenv_del(kenv *e);
kenv *kenv_copy(kenv *e);

kval *kval_lambda(kval *formals, kval *body) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_FUNC;
  v->builtin = NULL;
  v->env = kenv_new();
  v->formals = formals;
  v->body = body;
  return v;
}

void kval_del(kval *v) {
  switch(v->type) {
    case KVAL_NUM:
      break;
    case KVAL_ERR:
      free(v->err);
      break;
    case KVAL_SYM:
      free(v->sym);
      break;
    case KVAL_OK:
      break;
    case KVAL_QEXPR:
    case KVAL_SEXPR:
      for(int i = 0; i < v->count; i++){
        kval_del(v->cell[i]);
      }
      free(v->cell);
      break;
    case KVAL_FUNC:
      if(!v->builtin) {
        kenv_del(v->env);
        kval_del(v->formals);
        kval_del(v->body);
      }
      break;
    case KVAL_STR:
      free(v->str);
      break;
  }
  free(v);
}

kval *kval_add(kval *v, kval *x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(kval*) * v->count);
  v->cell[v->count-1] = x;
  return v;
}

kval *kval_pop(kval *v, int i) {
  kval *x = v->cell[i];
  memmove(&v->cell[i], &v->cell[i+1], sizeof(kval*) * (v->count-i-1));

  v->count--;
  v->cell = realloc(v->cell, sizeof(kval*) * v->count);
  
  return x;
}

kval *kval_take(kval *v, int i) {
  kval *x = kval_pop(v, i);
  kval_del(v);
  return x;
}

kval *kval_join(kval *x, kval *y) {
  while(y->count) {
    x = kval_add(x, kval_pop(y, 0));
  }
  kval_del(y);
  return x;
}

kval *kval_copy(kval *v) {
  kval *x = malloc(sizeof(kval));
  x->type = v->type;
  switch(v->type){
    case KVAL_FUNC:
      if(v->builtin) {
        x->builtin = v->builtin;
      } else {
        x->builtin = NULL;
        x->env = kenv_copy(v->env);
        x->formals = kval_copy(v->formals);
        x->body = kval_copy(v->body);
      }
      break;
    case KVAL_NUM: x->num = v->num; break;
    case KVAL_ERR:
      x->err = malloc(strlen(v->err) + 1);
      strcpy(x->err, v->err);
      break;
    case KVAL_SYM:
      x->sym = malloc(strlen(v->sym) + 1);
      strcpy(x->sym, v->sym);
      break;
    case KVAL_STR:
      x->str = malloc(strlen(v->str) + 1);
      strcpy(x->str, v->str);
      break;
    case KVAL_SEXPR:
    case KVAL_QEXPR:
      x->count = v->count;
      x->cell = malloc(sizeof(kval*) * x->count);
      for(int i = 0; i < x->count; i++) {
        x->cell[i] = kval_copy(v->cell[i]);
      }
      break;
  }
  return x;
}

int kval_eq(kval *x, kval *y) {
  if(x->type != y->type) {
    return 0;
  }
  switch(x->type) {
    case KVAL_NUM: return x->num == y->num; break;
    case KVAL_ERR: return strcmp(x->err, y->err) == 0; break;
    case KVAL_SYM: return strcmp(x->sym, y->sym) == 0; break;
    case KVAL_STR: return strcmp(x->str, y->str) == 0; break;
    case KVAL_FUNC:
      if(x->builtin || y->builtin) {
        return x->builtin == y->builtin;
      } else {
        return kval_eq(x->formals, y->formals) && kval_eq(x->body, y->body);
      }
      break;
    case KVAL_QEXPR:
    case KVAL_SEXPR:
      if(x->count != y->count) {return 0;}
      for(int i = 0; i < x->count; i++) {
        if(!kval_eq(x->cell[i], y->cell[i])) {return 0;}
      } 
      return 1;
      break;
  }
  return 0;
}

kenv *kenv_new(void) {
  kenv *e = malloc(sizeof(kenv));
  e->par = NULL;
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
}

void kenv_del(kenv *e) {
  for(int i = 0; i < e->count; i++) {
    free(e->syms[i]);
    kval_del(e->vals[i]);
  }
  free(e->syms);
  free(e->vals);
  free(e);
}

kval *kenv_get(kenv *e, kval *k) {
  for(int i = 0; i < e->count; i++) {
    if(strcmp(e->syms[i], k->sym) == 0) {
      return kval_copy(e->vals[i]);
    }
  }

  if(e->par) {
    return kenv_get(e->par, k);
  } else {
    return kval_err("Unbound Symbol! (%s)", k->sym);
  }
}

void kenv_put(kenv *e, kval *k, kval *v) {
  for(int i = 0; i < e->count; i++){
    if(strcmp(e->syms[i], k->sym) == 0) {
      kval_del(e->vals[i]);
      e->vals[i] = kval_copy(v);
      return;
    }
  }

  e->count++;
  e->vals = realloc(e->vals, sizeof(kval*) * e->count);
  e->syms = realloc(e->syms, sizeof(char*) * e->count);

  e->vals[e->count - 1] = kval_copy(v);
  e->syms[e->count - 1] = malloc(strlen(k->sym) + 1);
  strcpy(e->syms[e->count - 1], k->sym);
}

kenv *kenv_copy(kenv *e) {
  kenv *n = malloc(sizeof(kenv));
  n->par = e->par;
  n->count = e->count;
  n->syms = malloc(sizeof(char*) * n->count);
  n->vals = malloc(sizeof(kval*) * n->count);
  for(int i = 0; i < e->count; i++) {
    n->syms[i] = malloc(strlen(e->syms[i]) + 1);
    strcpy(n->syms[i], e->syms[i]);
    n->vals[i] = kval_copy(e->vals[i]);
  }
  return n;
}

void kenv_def(kenv *e, kval *k, kval *v) {
  while(e->par) {e = e->par;}
  kenv_put(e,k,v);
}

void print_kval(kval *v);

void print_kval_expr(kval *v, char open, char close) {
  putchar(open);
  for(int i = 0; i < v->count; i++) {
    print_kval(v->cell[i]);
    if(i != (v->count-1)) {
      putchar(' ');
    }
  }
  putchar(close);
}

void print_kval_str(kval *v) {
  char *escaped = malloc(strlen(v->str) + 1);
  strcpy(escaped, v->str);
  escaped = mpcf_escape(escaped);
  printf("\"%s\"", escaped);
  free(escaped);
}

void print_kval(kval *v) {
  switch(v->type) {
    case KVAL_NUM: printf("%g", v->num); break;
    case KVAL_ERR: printf("Error: %s", v->err); break;
    case KVAL_SYM: printf("%s", v->sym); break;
    case KVAL_STR: print_kval_str(v); break;
    case KVAL_SEXPR: print_kval_expr(v, '(', ')'); break;
    case KVAL_QEXPR: print_kval_expr(v, '{', '}'); break;
    case KVAL_OK: break;
    case KVAL_FUNC:
      if(v->builtin) {
        printf("<builtin function>");
      } else {
        printf("(\\ ");
        print_kval(v->formals);
        putchar(' ');
        print_kval(v->body);
        putchar(')');
      }
      break;
  }
}

void println_kval(kval *v){
  print_kval(v);
  putchar('\n');
}

kval *kval_eval(kenv *e, kval *v);
kval *kval_read(mpc_ast_t *t);

kval *builtin_head(kenv *e ,kval *a) {
  KDELWHENFALSE_NUM("head", a, 1);
  KDELWHENFALSE_TYPE("head", a, 0, KVAL_QEXPR);
  KDELWHENFALSE_NOT_EMPTY("head", a, 0);

  kval *v = kval_take(a, 0);
  while(v->count > 1) {kval_del(kval_pop(v,1));}
  return v;
}

kval *builtin_tail(kenv *e ,kval *a) {
  KDELWHENFALSE_NUM("tail", a, 1);
  KDELWHENFALSE_TYPE("tail", a, 0, KVAL_QEXPR);
  KDELWHENFALSE_NOT_EMPTY("tail", a, 0);

  kval *v = kval_take(a, 0);
  kval_del(kval_pop(v, 0));
  return v;
}

kval *builtin_list(kenv *e ,kval *a) {
  a->type = KVAL_QEXPR;
  return a;
}

kval *builtin_eval(kenv *e ,kval *a) {
  KDELWHENFALSE_NUM("eval", a, 1);
  KDELWHENFALSE_TYPE("eval", a, 0, KVAL_QEXPR);

  kval *x = kval_take(a, 0);
  x->type = KVAL_SEXPR;
  return kval_eval(e, x);
}

kval *builtin_join(kenv *e ,kval *a) {
  for(int i = 0; i < a->count; i++) {
    KDELWHENFALSE_TYPE("join", a, i, KVAL_QEXPR);
  }

  kval *x = kval_pop(a, 0);
  while(a->count) {
    x = kval_join(x, kval_pop(a, 0));
  }

  kval_del(a);
  return x;
}

kval *builtin_init(kenv *e ,kval *a) {
  KDELWHENFALSE_NUM("init", a, 1);
  KDELWHENFALSE_TYPE("init", a, 0, KVAL_QEXPR);
  KDELWHENFALSE_NOT_EMPTY("init", a, 0);

  kval *x = kval_take(a, 0);
  kval_take(x, x->count - 1);
  return x;
}

kval *builtin_cons(kenv *e ,kval* a) {
  KDELWHENFALSE(a, a->cell[1]->type == KVAL_QEXPR, "Function 'cons' recieved incorrect type!");
  KDELWHENFALSE(a, a->count == 2, "Function 'cons' recieved too many/less arguments!");
  kval *x = kval_pop(a, 1);
  a->type = KVAL_QEXPR;
  return kval_join(a, x);
}

kval *builtin_op(kenv *e, kval *a, char *op) {
  for(int i = 0; i < a->count; i++) {
    KDELWHENFALSE_TYPE(op, a, i, KVAL_NUM);
  }

  kval *x = kval_pop(a, 0);

  if((strcmp(op, "-") == 0) && a->count == 0) {
    x->num = -x->num;
  }

  while(a->count > 0) {
    kval *y = kval_pop(a, 0);
    if(strcmp(op, "+") == 0) {x->num += y->num;}
    if(strcmp(op, "-") == 0) {x->num -= y->num;}
    if(strcmp(op, "*") == 0) {x->num *= y->num;}
    if(strcmp(op, "/") == 0) {
      if(y->num == 0) {
        kval_del(x); kval_del(y);
        x = kval_err("Division by Zero..");
        break;
      }
      x->num /= y->num;
    }
    if(strcmp(op, "%") == 0) {
      if(x->num == floorf(x->num) && y->num == floorf(y->num)){
        x->num = (int)x->num%(int)y->num;
      } else {
        x = kval_err("Can't perform Modulo (\"%\") on non Integer values!");
      }
    }
    if(strcmp(op, "^") == 0) {x->num = pow(x->num,y->num);}
    kval_del(y);
  }
  kval_del(a);
  return x;
}

kval *builtin_add(kenv *e, kval *a) {
  return builtin_op(e, a, "+");
}

kval *builtin_sub(kenv *e, kval *a) {
  return builtin_op(e, a, "-");
}

kval *builtin_mul(kenv *e, kval *a) {
  return builtin_op(e, a, "*");
}

kval *builtin_div(kenv *e, kval *a) {
  return builtin_op(e, a, "/");
}

kval *builtin_mod(kenv *e, kval *a) {
  return builtin_op(e, a, "%");
}

kval *builtin_pow(kenv *e, kval *a) {
  return builtin_op(e, a, "^");
}

kval *builtin_sqrt(kenv *e, kval *a) {
  kval *x = kval_pop(a, 0);
  x->num = sqrt(x->num);
  kval_del(a);
  return x;
}

kval *builtin_var(kenv *e, kval *a, char *func) {
  KDELWHENFALSE_TYPE(func, a, 0, KVAL_QEXPR);
  
  kval *syms = a->cell[0];

  for(int i = 0; i < syms->count; i++) {
    KDELWHENFALSE(a, syms->cell[i]->type == KVAL_SYM, "Function %s can't define non-symbol! Got %s but expected %s."
    ,func, ktype_name(syms->cell[i]->type), ktype_name(KVAL_SYM));
  }

  KDELWHENFALSE(a, (syms->count == a->count - 1), 
  "Function '%s' passed too many arguments for symbols. Got %i but expected %i",
  func, syms->count, a->count - 1);

  for(int i = 0; i < syms->count; i++) {
    if(strcmp(func, "def") == 0) {
      kenv_def(e, syms->cell[i], a->cell[i+1]);
    }
    if(strcmp(func, "=") == 0) {
      kenv_put(e, syms->cell[i], a->cell[i+1]);
    }
  }

  kval_del(a);
  return kval_sexpr();
}

kval *builtin_def(kenv *e, kval* a) {
  return builtin_var(e, a, "def");
}

kval *builtin_put(kenv *e, kval *a) {
  return builtin_var(e, a, "=");
}

kval *builtin_exit(kenv *e, kval *a) {
  KDELWHENFALSE_TYPE("exit", a, 0, KVAL_NUM);
  KDELWHENFALSE_NUM("exit", a, 1);
  kval *v = kval_take(a, 0);
  exit_main = v->num;
  return kval_num(v->num);
}

kval *builtin_print_env(kenv *e, kval *a) {
  KDELWHENFALSE_TYPE("print_env", a, 0, KVAL_NUM);
  KDELWHENFALSE_NUM("print_env", a, 1);
  KDELWHENFALSE(a, a->cell[0]->num>=0, "Function 'print_env' requires a positive argument!");
  kval *v = kval_take(a, 0);
  for(int i = 0; i < (v->num == 0 ? e->count : v->num); i++) {
    fputs("Key: ", stdout);
    puts(e->syms[i]);
    fputs("Value: ", stdout);
    println_kval(e->vals[i]);
  }
  kval_del(v);
  return kval_sym("END");
}

kval *builtin_lambda(kenv *e, kval *a) {
  KDELWHENFALSE_NUM("\\", a, 2);
  KDELWHENFALSE_TYPE("\\", a, 0, KVAL_QEXPR);
  KDELWHENFALSE_TYPE("\\", a, 1, KVAL_QEXPR);
  for(int i = 0; i < a->cell[0]->count; i++) {
    KDELWHENFALSE(a, a->cell[0]->cell[i]->type == KVAL_SYM, "Can't define non-symbol. Got %s but expected %s",
    ktype_name(a->cell[0]->cell[i]->type), ktype_name(KVAL_SYM));
  }
  kval *formals = kval_pop(a, 0);
  kval *body = kval_take(a, 0);

  return kval_lambda(formals, body);
}

kval *builtin_clear(kenv *e, kval *a) {
  system("@cls||clear");
  return kval_ok();
}

kval *builtin_compord(kenv *e, kval *a, char *op) {
  KDELWHENFALSE_NUM(op, a, 2);
  KDELWHENFALSE_TYPE(op, a, 0, KVAL_NUM);
  KDELWHENFALSE_TYPE(op, a, 1, KVAL_NUM);
  int r;
  if(strcmp(op, "<") == 0) {
    r = a->cell[0]->num < a->cell[1]->num;
  }
  if(strcmp(op, ">") == 0) {
    r = a->cell[0]->num > a->cell[1]->num;    
  }
  if(strcmp(op, "<=") == 0) {
    r = a->cell[0]->num <= a->cell[1]->num;
  }
  if(strcmp(op, ">=") == 0) {
    r = a->cell[0]->num >= a->cell[1]->num;
  }
  kval_del(a);
  return kval_num(r);
}

kval *builtin_lt(kenv *e, kval *a) {
  return builtin_compord(e, a, "<");
}
kval *builtin_gt(kenv *e, kval *a) {
  return builtin_compord(e, a, ">");
}
kval *builtin_gte(kenv *e, kval *a) {
  return builtin_compord(e, a, ">=");
}
kval *builtin_lte(kenv *e, kval *a) {
  return builtin_compord(e, a, "<=");
}

kval *builtin_compeq(kenv *e, kval *a, char *op) {
  KDELWHENFALSE_NUM(op, a, 2);
  int r;
  if(strcmp(op, "==") == 0) {
    r =  kval_eq(a->cell[0], a->cell[1]);
  }
  if(strcmp(op, "!=") == 0) {
    r = !kval_eq(a->cell[0], a->cell[1]);
  }
  kval_del(a);
  return kval_num(r);
}

kval *builtin_eq(kenv *e, kval *a) {
  return builtin_compeq(e, a, "==");
}

kval *builtin_neq(kenv *e, kval *a) {
  return builtin_compeq(e, a, "!=");
}

kval *builtin_if(kenv *e, kval *a) {
  KDELWHENFALSE_NUM("if", a, 3);
  KDELWHENFALSE_TYPE("if", a, 0, KVAL_NUM);
  KDELWHENFALSE_TYPE("if", a, 1, KVAL_QEXPR);
  KDELWHENFALSE_TYPE("if", a, 2, KVAL_QEXPR);
  kval *x;
  a->cell[1]->type = KVAL_SEXPR;
  a->cell[2]->type = KVAL_SEXPR;
  if(a->cell[0]->num) {
    x = kval_eval(e, kval_pop(a, 1));
  } else {
    x = kval_eval(e, kval_pop(a, 2));
  }
  kval_del(a);
  return x;
}

kval *builtin_print(kenv *e, kval *a) {
  for(int i = 0; i < a->count; i++) {
    print_kval(a->cell[i]);
    putchar(' ');
  }
  putchar('\n');
  kval_del(a);
  return kval_ok();
}

kval *builtin_error(kenv *e, kval *a) {
  KDELWHENFALSE_NUM("error", a, 1);
  KDELWHENFALSE_TYPE("error", a, 0, KVAL_STR);
  kval *err = kval_err(a->cell[0]->str);
  kval_del(a);
  return err;
}

kval *builtin_load(kenv *e, kval *a) {
  KDELWHENFALSE_NUM("load", a, 1);
  KDELWHENFALSE_TYPE("load", a, 0, KVAL_STR);
  mpc_result_t r;
  if(mpc_parse_contents(a->cell[0]->str, Kek, &r)) {
    kval *expr = kval_read(r.output);
    mpc_ast_delete(r.output);
    while(expr->count) {
      kval *x = kval_eval(e, kval_pop(expr, 0));
      if(x->type == KVAL_ERR) {println_kval(x);}
      kval_del(x);
    }
    kval_del(expr);
    kval_del(a);
    return kval_ok();
  } else {
    char *err_msg = mpc_err_string(r.error);
    mpc_err_delete(r.error);
    kval *err = kval_err("Couldn't load Library %s", err_msg);
    free(err_msg);
    kval_del(a);
    return err;
  }
}

kval *kval_call(kenv *e, kval *f, kval *a) {
  if(f->builtin) {
    return f->builtin(e, a);
  }
  int givenargs = a->count;
  int totalargs = f->formals->count;

  while(a->count) {
    if(f->formals->count == 0) {
      kval_del(a);
      return kval_err("Function passed too many arguments. Got %i but expected %i.", givenargs, totalargs);
    }
    kval *sym = kval_pop(f->formals, 0);
    if(strcmp(sym->sym, "&") == 0) {
      if(f->formals->count != 1) {
        kval_del(a);
        return kval_err("Invalid function format. Symbol '&' should only be followed by one Symbol.");
      }
      kval *nsym = kval_pop(f->formals, 0);
      kenv_put(f->env, nsym, builtin_list(e, a));
      kval_del(sym);
      kval_del(nsym);
      break;
    }
    kval *val = kval_pop(a, 0);
    kenv_put(f->env, sym, val);
    kval_del(sym);
    kval_del(val);
  }
  kval_del(a);
  if(f->formals->count > 0 && strcmp(f->formals->cell[0]->sym, "&") == 0) {
    if(f->formals->count != 2) {
      return kval_err("Invalid function format. Symbol '&' should be followed by one Symbol.");
    }
    kval_del(kval_pop(f->formals, 0));
    kval *sym = kval_pop(f->formals, 0);
    kval *val = kval_qexpr();
    kenv_put(f->env, sym, val);
    kval_del(sym);
    kval_del(val);
  }
  if(f->formals->count == 0) {
    f->env->par = e;
    return builtin_eval(f->env, kval_add(kval_sexpr(), kval_copy(f->body)));
  } else {
    return kval_copy(f);
  }
}

void kenv_add_builtin(kenv *e, char *name, kbuiltin function) {
  kval *k = kval_sym(name);
  kval *v = kval_func(function);
  kenv_put(e, k, v);
  kval_del(k);
  kval_del(v);
}

void kenv_add_builtins(kenv *e) {
  kenv_add_builtin(e, "list", builtin_list);
  kenv_add_builtin(e, "head", builtin_head);
  kenv_add_builtin(e, "tail", builtin_tail);
  kenv_add_builtin(e, "eval", builtin_eval);
  kenv_add_builtin(e, "join", builtin_join);
  kenv_add_builtin(e, "init", builtin_init);
  kenv_add_builtin(e, "cons", builtin_cons);
  kenv_add_builtin(e, "def", builtin_def);
  kenv_add_builtin(e, "exit", builtin_exit);
  kenv_add_builtin(e, "print_env", builtin_print_env);
  kenv_add_builtin(e, "\\", builtin_lambda);
  kenv_add_builtin(e, "=", builtin_put);
  kenv_add_builtin(e, "clear", builtin_clear);
  kenv_add_builtin(e, "if", builtin_if);
  kenv_add_builtin(e, "load", builtin_load);
  kenv_add_builtin(e, "error", builtin_error);
  kenv_add_builtin(e, "print", builtin_print);

  kenv_add_builtin(e, "+", builtin_add);
  kenv_add_builtin(e, "-", builtin_sub);
  kenv_add_builtin(e, "*", builtin_mul);
  kenv_add_builtin(e, "/", builtin_div);
  kenv_add_builtin(e, "%", builtin_mod);
  kenv_add_builtin(e, "^", builtin_pow);
  kenv_add_builtin(e, "sqrt", builtin_sqrt);
  kenv_add_builtin(e, "<", builtin_lt);
  kenv_add_builtin(e, ">", builtin_gt);
  kenv_add_builtin(e, "<=", builtin_lte);
  kenv_add_builtin(e, ">=", builtin_gte);
  kenv_add_builtin(e, "==", builtin_eq);
  kenv_add_builtin(e, "!=", builtin_neq);
}

kval *kval_eval_sexpr(kenv *e, kval* v) {
  for(int i = 0; i < v->count; i++) {
    v->cell[i] = kval_eval(e, v->cell[i]);
  }

  for(int i = 0; i < v->count; i++) {
    if(v->cell[i]->type == KVAL_ERR) {return kval_take(v, i);}
  }

  if(v->count == 0) {return v;}
  if(v->count == 1) {return kval_take(v,0);}

  kval *f = kval_pop(v,0);
  if(f->type != KVAL_FUNC) {
    kval *err = kval_err("S-Expression starts with incorrect type. Got %s but expected %s.",
    ktype_name(f->type), ktype_name(KVAL_FUNC));
    kval_del(f); kval_del(v);
    return err;
  }

  kval *result = kval_call(e, f, v);
  kval_del(f);
  return result;
}

kval *kval_eval(kenv *e, kval *v) {
  if(v->type == KVAL_SYM) {
    kval *x = kenv_get(e, v);
    kval_del(v);
    return x;
  }
  if(v->type == KVAL_SEXPR) {return kval_eval_sexpr(e, v);}
  return v;
}

kval *kval_read_num(mpc_ast_t *t) {
  errno = 0;
  double x = atof(t->contents);
  return errno != ERANGE ? kval_num(x) : kval_err("Invalid Number!");
}

kval *kval_read_str(mpc_ast_t *t) {
  t->contents[strlen(t->contents) - 1] = '\0';
  char *unescaped = malloc(strlen(t->contents + 1) + 1);
  strcpy(unescaped, t->contents + 1);
  unescaped = mpcf_unescape(unescaped);
  kval *str = kval_str(unescaped);
  free(unescaped);
  return str;
}

kval *kval_read(mpc_ast_t *t) {
  if(strstr(t->tag, "number") || strstr(t->tag, "double")) {return kval_read_num(t);}
  if(strstr(t->tag, "symbol")) {return kval_sym(t->contents);}
  if(strstr(t->tag, "string")) {return kval_read_str(t);}
  kval *x = NULL;
  if(strcmp(t->tag, ">") == 0) {x = kval_sexpr();}
  if(strstr(t->tag, "sexpr")) {x = kval_sexpr();}
  if(strstr(t->tag, "qexpr")) {x = kval_qexpr();}
  for(int i = 0; i < t->children_num; i++) {
    if(strstr(t->children[i]->tag, "comment")) {
      continue;
    }
    if(strcmp(t->children[i]->contents, "(") == 0) {
      continue;
    }
    if(strcmp(t->children[i]->contents, ")") == 0) {
      continue;
    }
    if(strcmp(t->children[i]->contents, "{") == 0) {
      continue;
    }
    if(strcmp(t->children[i]->contents, "}") == 0) {
      continue;
    }
    if(strcmp(t->children[i]->tag, "regex") == 0) {
      continue;
    }
    x = kval_add(x, kval_read(t->children[i]));
  }
  return x;
}

int main(int argc, char **argv) {
  Number = mpc_new("number");
  Double = mpc_new("double");
  Symbol = mpc_new("symbol");
  String = mpc_new("string");
  Comment = mpc_new("comment");
  Sexpr  = mpc_new("sexpr");
  Qexpr  = mpc_new("qexpr");
  Expr   = mpc_new("expr");
  Kek  = mpc_new("kek");
  
  mpca_lang(MPCA_LANG_DEFAULT,
    " \
      double : /-?[0-9]+[.][0-9]+/ ; \
      number : /-?[0-9]+/ ; \
      string  : /\"(\\\\.|[^\"])*\"/ ; \
      comment : /\\/\\/[^\\r\\n]*/ ; \
      symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&%^]+/; \
      sexpr  : '(' <expr>* ')' ; \
      qexpr  : '{' <expr>* '}' ; \
      expr   : <double> | <number> | <comment> | <symbol> | <string> | <sexpr> | <qexpr> ; \
      kek  : /^/ <expr>* /$/ ; \
    ",
    Double, Number, Symbol, String, Comment, Sexpr, Qexpr, Expr, Kek);
  
  
  kenv *e = kenv_new();
  kenv_add_builtins(e);

  if(argc == 1) {
    puts("KekLang v0.0.7");
    puts("Press Ctrl+c to Exit\n");

    while (1) {
    
      fputs("KekLang> ", stdout);
      fgets(input, 2048, stdin);
      
      mpc_result_t r;
      if (mpc_parse("<stdin>", input, Kek, &r)) {
        kval* x = kval_eval(e, kval_read(r.output));
        println_kval(x);
        kval_del(x);
        mpc_ast_delete(r.output);
      } else {    
        mpc_err_print(r.error);
        mpc_err_delete(r.error);
      }
      
      if(exit_main != -1){
        break;
      }
    }
  }

  if(argc >= 2) {
    for(int i = 1; i < argc; i++) {
      kval *args = kval_add(kval_sexpr(), kval_str(argv[i]));
      kval *x = builtin_load(e, args);
      if(x->type == KVAL_ERR) {
        println_kval(x);
      }
      kval_del(x);
    }
  }
  
  puts("Terminating..");
  kenv_del(e);
  mpc_cleanup(9, Double, Number, Symbol,String, Comment, Sexpr, Qexpr, Expr, Kek);
  if(exit_main != -1) {
    return exit_main;
  }
  return 0;
}

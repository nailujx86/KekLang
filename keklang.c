#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <math.h>
#include "mpc.h"

static char input[2084];

typedef struct kval {
  int type;
  double num;
  char *err;
  char *sym;
  int count;
  struct kval **cell;
} kval;

enum {KVAL_ERR, KVAL_NUM, KVAL_SYM, KVAL_SEXPR, KVAL_QEXPR};
enum {KERR_BAD_NUM, KERR_BAD_OP, KERR_DIV_ZERO};

kval *kval_num(double x) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_NUM;
  v->num = x;
  return v;
}

kval *kval_err(char* m) {
  kval *v = malloc(sizeof(kval));
  v->type = KVAL_ERR;
  v->err = malloc(strlen(m) + 1);
  strcpy(v->err, m);
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
    case KVAL_QEXPR:
    case KVAL_SEXPR:
      for(int i = 0; i < v->count; i++){
        kval_del(v->cell[i]);
      }
      free(v->cell);
      break;
  }
  free(v);
}

kval *kval_read_num(mpc_ast_t *t) {
  errno = 0;
  double x = atof(t->contents);
  return errno != ERANGE ? kval_num(x) : kval_err("Invalid Number!");
}

kval *kval_add(kval *v, kval *x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(kval*) * v->count);
  v->cell[v->count-1] = x;
  return v;
}

kval *kval_read(mpc_ast_t *t) {
  if(strstr(t->tag, "number") || strstr(t->tag, "double")) {return kval_read_num(t);}
  if(strstr(t->tag, "symbol")) {return kval_sym(t->contents);}

  kval *x = NULL;
  if(strcmp(t->tag, ">") == 0) {x = kval_sexpr();}
  if(strstr(t->tag, "sexpr")) {x = kval_sexpr();}

  for(int i = 0; i < t->children_num; i++) {
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

void print_kval(kval *v) {
  switch(v->type) {
    case KVAL_NUM: printf("%g", v->num); break;
    case KVAL_ERR: printf("Error: %s", v->err); break;
    case KVAL_SYM: printf("%s", v->sym); break;
    case KVAL_SEXPR: print_kval_expr(v, '(', ')'); break;
    case KVAL_QEXPR: print_kval_expr(v, '{', '}'); break;
  }
}

void println_kval(kval *v){
  print_kval(v);
  putchar('\n');
}

int number_of_nodes(mpc_ast_t *t) {
  if(t->children_num == 0) {return 1;}
  if(t->children_num >=1) {
    int nodes = 1;
    for(int i = 0; i < t->children_num; i++){
      nodes += number_of_nodes(t->children[i]);
    }
    return nodes;
  }
  return 0;
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

kval *builtin_op(kval *a, char *op) {
  for(int i = 0; i < a->count; i++) {
    if(a->cell[i]->type != KVAL_NUM) {
      kval_del(a);
      return kval_err("Can't operate on non number!");
    }
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

kval *kval_eval_sexpr(kval* v);

kval *kval_eval(kval *v) {
  if(v->type == KVAL_SEXPR) {return kval_eval_sexpr(v);}
  return v;
}

kval *kval_eval_sexpr(kval* v) {
  for(int i = 0; i < v->count; i++) {
    v->cell[i] = kval_eval(v->cell[i]);
  }

  for(int i = 0; i < v->count; i++) {
    if(v->cell[i]->type == KVAL_ERR) {return kval_take(v, i);}
  }

  if(v->count == 0) {return v;}
  if(v->count == 1) {return kval_take(v,0);}

  kval *f = kval_pop(v,0);
  if(f->type != KVAL_SYM) {
    kval_del(f); kval_del(v);
    return kval_err("S-expr doesn't start with a symbol!");
  }

  kval *result = builtin_op(v, f->sym);
  kval_del(f);
  return result;
}

int main(int argc, char **argv) {
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Double = mpc_new("double");
  mpc_parser_t* Symbol = mpc_new("symbol");
  mpc_parser_t* Sexpr  = mpc_new("sexpr");
  mpc_parser_t* Qexpr  = mpc_new("qexpr");
  mpc_parser_t* Expr   = mpc_new("expr");
  mpc_parser_t* Kek  = mpc_new("kek");
  
  mpca_lang(MPCA_LANG_DEFAULT,
    " \
      double : /-?[0-9]+[.][0-9]+/ ; \
      number : /-?[0-9]+/ ; \
      symbol : '+' | '-' | '*' | '/' | '%' | '^' ; \
      sexpr  : '(' <expr>* ')' ; \
      qexpr  : '{' <expr>* '}' ; \
      expr   : <double> | <number> | <symbol> | <sexpr> ; \
      kek  : /^/ <expr>* /$/ ; \
    ",
    Double, Number, Symbol, Sexpr, Qexpr, Expr, Kek);
  
  puts("KekLang v0.0.3");
  puts("Press Ctrl+c to Exit\n");
  
  while (1) {
  
    fputs("KekLang> ", stdout);
    fgets(input, 2048, stdin);
    
    mpc_result_t r;
    if (mpc_parse("<stdin>", input, Kek, &r)) {
      kval* x = kval_eval(kval_read(r.output));
      println_kval(x);
      kval_del(x);
      mpc_ast_delete(r.output);
    } else {    
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    
  }
  
  mpc_cleanup(7, Double, Number, Symbol, Sexpr, Qexpr, Expr, Kek);
  
  return 0;

}
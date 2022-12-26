#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>
#include <inttypes.h>
#include <errno.h>

#if !defined(__OPTIMIZE__) && !defined(DEBUG)
#define DEBUG
#endif

// ============================================================================
//                                   DynArr
// ============================================================================

typedef struct DynArr
{
    size_t size;
    size_t capacity;
    size_t elem_size;
    void *data;
} DynArr;

enum
{ 
    START_ARR_SIZE = 1024,
    START_MULTIPLIER = 2,
    DIMINUTION_COEFFICIENT = 4
};

static DynArr
da_construct_size(size_t elem_size, size_t initial_cap)
{
    DynArr da;
    da.size = 0;
    da.elem_size = elem_size;
    da.data = malloc(initial_cap * elem_size);
    if (da.data == NULL) {
        abort();
    } else {
        da.capacity = initial_cap;
    }
    return da;
}

static DynArr
da_construct(size_t elem_size)
{
    return da_construct_size(elem_size, START_ARR_SIZE);
}

static void
da_destruct(DynArr *da)
{
    free(da->data);
    da->data = NULL;
    da->size = da->capacity = 0;
}

static bool
da_expand_if_possible(DynArr *da)
{ 
    if (da == NULL || da->elem_size == 0) {
        return false;
    }
    if (da->capacity == 0) {
        *da = da_construct(da->elem_size);
        return da->data != NULL;
    }
    double multiplier = START_MULTIPLIER;
    size_t new_capacity = da->capacity * multiplier;
#ifdef DEBUG
    fprintf(stderr, "\ndebug: expand_if_possible: bufer resize from %ld to %ld\n", 
                    da->capacity, new_capacity);
#endif
    int *new_arr = realloc(da->data, new_capacity * da->elem_size);
    while (new_arr == NULL && new_capacity != da->capacity) {
        multiplier -= 1;
        multiplier /= DIMINUTION_COEFFICIENT;
        multiplier += 1;
        new_capacity = da->capacity * multiplier;
#ifdef DEBUG
        fprintf(stderr, "\ndebug: expand_if_possible: realloc returned NULL,\
                        another atempt: multiplier = %f, new_capacity = %ld\n",
                        multiplier, new_capacity);
#endif
        new_arr = realloc(da->data, new_capacity * da->elem_size);
    }
    if (new_capacity == da->capacity) {
#ifdef DEBUG
        fprintf(stderr, "\nerror: expand_if_possible: cannot allocate memory\n");
#endif
        return false;
    } 
    da->data = new_arr;
    da->capacity = new_capacity;
    return true;
}


static bool
da_push_back(DynArr *da, const void *val)
{
    if (da->size == da->capacity && da_expand_if_possible(da) == false) {
        abort();
    }
    memcpy(da->data + da->size++ * da->elem_size, val, da->elem_size);
    return true;
}

static void *
da_at(const DynArr *da, size_t index)
{
    if (da->size <= index) {
        abort();
    }
    return (DynArr*)(da->data + index * da->elem_size);
}

static void *
da_back(DynArr *da)
{
    if (da->size) {
        return da_at(da, da->size - 1);
    }
    abort();
}

static bool
da_pop_back(DynArr *da)
{
    if (da->size) {
        --da->size;
        return true;
    }
    abort();
}

void da_remove(DynArr * da, size_t i)
{
    void * to_replace = da_at(da, i);
    void * last_elem = da_back(da);
    memcpy(to_replace, last_elem, da->elem_size);
    da_pop_back(da);
}

DynArr da_clone(const DynArr * da)
{
    DynArr new_da = *da;
    new_da.data = malloc(new_da.capacity * new_da.elem_size);
    memcpy(new_da.data, da->data, new_da.size * new_da.elem_size);
    return new_da;
}

// ============================================================================
//                                   Clause
// ============================================================================

#define DEFAULT_CLAUSE_SIZE 3

typedef struct Clause
{
    DynArr literals;
} Clause;

Clause cl_parse(FILE * in, int32_t max_literal)
{
    Clause cl;
    cl.literals = da_construct_size(sizeof(int32_t), DEFAULT_CLAUSE_SIZE);
    int32_t literal;
    do
    {
        int res = fscanf(in, "%"SCNd32, &literal);
        bool invalid = literal < -max_literal || max_literal < literal;
        if (errno || res != 1 || invalid)
            abort();
        if (literal)
            da_push_back(&cl.literals, &literal);
    } while (literal);
    return cl;
}

void cl_destruct(Clause * cl)
{
    da_destruct(&cl->literals);
}

Clause cl_clone(const Clause * cl)
{
    Clause new_cl;
    new_cl.literals = da_clone(&cl->literals);
    return new_cl;
}

void cl_print(const Clause * cl, FILE * out)
{
    //if (cl->literals.size == 0)
    //    return;
    
    fputc('(', out);

    bool first = true;
    for (size_t i = 0; i < cl->literals.size; ++i)
    {
        if (!first)
            fputs(" | ", out);
        first = false;

        int32_t literal = *(int32_t*)da_at(&cl->literals, i);
        if (literal < 0)
        {
            fputc('!', out);
            literal = -literal;
        }
        fprintf(out, "%"PRId32, literal);
    }

    fputc(')', out);
}

bool cl_always_true(const Clause * cl)
{
    for (size_t i = 0; i < cl->literals.size; ++i)
    {
        int32_t literal1 = *(int32_t*)da_at(&cl->literals, i);
        for (size_t j = i+1; j < cl->literals.size; ++j)
        {
            int32_t literal2 = *(int32_t*)da_at(&cl->literals, j);
            if (literal1 == -literal2)
                return true;
        }
    }
    return false;
}

int cl_has_literal(const Clause * cl, int32_t lit)
{
    for (size_t i = 0; i < cl->literals.size; ++i)
    {
        int32_t literal = *(int32_t*)da_at(&cl->literals, i);
        if (literal == lit)
            return 1;
        else if (literal == -lit)
            return -1;
    }
    return 0;
}

void cl_remove_literal(Clause * cl, int32_t lit)
{
    for (size_t i = 0; i < cl->literals.size; ++i)
    {
        int32_t literal = *(int32_t*)da_at(&cl->literals, i);
        if (literal == lit)
        {
            da_remove(&cl->literals, i);
            return;
        }
    }
}

// ============================================================================
//                                   CNF
// ============================================================================

typedef struct CNF
{
    size_t num_vars;
    DynArr clauses;
} CNF;

CNF cnf_parse(FILE * in, size_t num_vars, size_t num_clauses)
{
    CNF cnf;
    cnf.num_vars = num_vars;
    cnf.clauses = da_construct_size(sizeof(Clause), num_clauses);
    for (size_t i = 0; i < num_clauses; ++i)
    {
        Clause cl = cl_parse(in, num_vars);
        da_push_back(&cnf.clauses, &cl);
    }
    return cnf;
}

void cnf_destruct(CNF * cnf)
{
    for (size_t i = 0; i < cnf->clauses.size; ++i)
        cl_destruct(da_at(&cnf->clauses, i));
    da_destruct(&cnf->clauses);
}

CNF cnf_clone(const CNF * cnf)
{
    CNF new_cnf;
    new_cnf.num_vars = cnf->num_vars;
    new_cnf.clauses = da_construct_size(sizeof(Clause), cnf->clauses.size);
    new_cnf.clauses.size = cnf->clauses.size;
    for (size_t i = 0; i < new_cnf.clauses.size; ++i)
    {
        const Clause * cl = da_at(&cnf->clauses, i);
        Clause * new_cl = da_at(&new_cnf.clauses, i);
        *new_cl = cl_clone(cl);
    }
    return new_cnf;
}

void cnf_print(const CNF * cnf, FILE * out)
{
    if (cnf->clauses.size == 0)
    {
        fputs("Empty", out);
        return;
    }

    bool first = true;
    for (size_t i = 0; i < cnf->clauses.size; ++i)
    {
        if (!first)
            fputs(" & ", out);
        first = false;
        cl_print(da_at(&cnf->clauses, i), out);
    }
}

void cnf_remove_tautology(CNF * cnf)
{
    size_t i = 0;
    while (i < cnf->clauses.size)
    {
        Clause * cl = da_at(&cnf->clauses, i);
        if (cl_always_true(cl))
        {
            cl_destruct(cl);
            da_remove(&cnf->clauses, i);
        }
        else
        {
            ++i;
        }
    }
}

size_t cnf_find_first_trivial_clause(const CNF * cnf)
{
    for (size_t i = 0; i < cnf->clauses.size; ++i)
    {
        const Clause * cl = da_at(&cnf->clauses, i);
        if (cl->literals.size == 1)
            return i;
    }
    return -1;
}

void cnf_propagate_unit(CNF * cnf, DynArr * literals_out)
{
    size_t triv_i = cnf_find_first_trivial_clause(cnf);
    while (triv_i != (size_t)-1)
    {
        const Clause * cl = da_at(&cnf->clauses, triv_i);
        int32_t literal = *(int32_t*)da_at(&cl->literals, 0);
        da_push_back(literals_out, &literal);
        
        size_t i = 0;
        while (i < cnf->clauses.size)
        {
            Clause * cl = da_at(&cnf->clauses, i);
            if (cl_has_literal(cl, literal) == 1)
            {
                cl_destruct(cl);
                da_remove(&cnf->clauses, i);
            }
            else
            {
                ++i;
            }
        }

        for (size_t i = 0; i < cnf->clauses.size; ++i)
        {
            Clause * cl = da_at(&cnf->clauses, i);
            cl_remove_literal(cl, -literal);
        }

        triv_i = cnf_find_first_trivial_clause(cnf);
    }
}

void cnf_find_pure_literals(const CNF * cnf, DynArr * literals_out)
{
    int8_t signs[cnf->num_vars + 1];
    memset(signs, 0, sizeof(signs));
    for (size_t i = 0; i < cnf->clauses.size; ++i)
    {
        const Clause * cl = da_at(&cnf->clauses, i);
        for (size_t j = 0; j < cl->literals.size; ++j)
        {
            int32_t literal = *(int32_t*)da_at(&cl->literals, j);
            int8_t sign = literal > 0 ? 1 : -1;
            int32_t idx = literal > 0 ? literal : -literal;
            if (signs[idx] == 0)
                signs[idx] = sign;
            else if (signs[idx] != sign)
                signs[idx] = 2;
        }
    }

    for (size_t i = 1; i <= cnf->num_vars; ++i)
    {
        int32_t not_i = -i;
        if (signs[i] == 1)
            da_push_back(literals_out, &i);
        else if (signs[i] == -1)
            da_push_back(literals_out, &not_i);
    }
}

bool cnf_check_true(const CNF * cnf, int8_t * signs)
{
    size_t true_cl_num = 0;
    for (size_t i = 0; i < cnf->clauses.size; ++i)
    {
        const Clause * cl = da_at(&cnf->clauses, i);
        for (size_t j = 0; j < cl->literals.size; ++j)
        {
            int32_t literal = *(int32_t*)da_at(&cl->literals, j);
            int8_t sign = literal > 0 ? 1 : -1;
            int32_t idx = literal > 0 ? literal : -literal;
            if (signs[idx] == sign)
            {
                ++true_cl_num;
                break;
            }
        }
    }
    return true_cl_num == cnf->clauses.size;
}

// ============================================================================
//                                Problem
// ============================================================================

typedef struct Problem
{
    CNF cnf;
    DynArr interp;
} Problem;

Problem p_parse(FILE * in)
{
    // Skip comments
    int c = fgetc(in);
    while (c == 'c')
    {
        int skip;
        do
        {
            skip = fgetc(in);
        } while (skip != '\n' && skip != EOF);
        c = fgetc(in);
    }
    if (c == EOF)
        abort();
    ungetc(c, in);

    // Read format string
    char pstr[2];
    char format[32];
    uint32_t vars;
    uint32_t clauses;
    int res = fscanf(in, "%1s%31s%"SCNu32"%"SCNu32, pstr, format, &vars, &clauses);
    if (errno || res != 4)
        abort();
    if (strcmp(pstr, "p") || strstr(format, "cnf") == NULL)
        abort();

    Problem p;
    p.interp = da_construct_size(sizeof(uint32_t), vars);
    p.cnf = cnf_parse(in, vars, clauses);
    return p;
}

void p_print(const Problem * p, FILE * out)
{
    fputs("CNF: ", out);
    cnf_print(&p->cnf, out);
    fputs("\nTrue literals:", out);
    for (size_t i = 0; i < p->interp.size; ++i)
        fprintf(out, " %d", *(uint32_t*)da_at(&p->interp, i));
}

Problem p_clone(const Problem * p)
{
    Problem new_p;
    new_p.cnf = cnf_clone(&p->cnf);
    new_p.interp = da_clone(&p->interp);
    return new_p;
}

void p_destruct(Problem * p)
{
    cnf_destruct(&p->cnf);
    da_destruct(&p->interp);
}

bool p_check_interp_signs(const Problem * p, int8_t * signs)
{
    memset(signs, 0, p->cnf.num_vars + 1);
    for (size_t j = 0; j < p->interp.size; ++j)
    {
        int32_t literal = *(int32_t*)da_at(&p->interp, j);
        int8_t sign = literal > 0 ? 1 : -1;
        int32_t idx = literal > 0 ? literal : -literal;

        if (signs[idx] == 0)
            signs[idx] = sign;
        else if (signs[idx] != sign)
            return false;
    }
    return true;
}

int p_dpll_impl(Problem * p, int32_t * next_var)
{
#ifdef DEBUG
    fprintf(stderr, "\nDPLL, depth %zu, %zu:\t", p->interp.size, p->cnf.clauses.size);
    p_print(p, stderr);
#endif

    cnf_propagate_unit(&p->cnf, &p->interp);
#ifdef DEBUG
    fprintf(stderr, "\n\tAfter UP %zu, %zu:\t", p->interp.size, p->cnf.clauses.size);
    p_print(p, stderr);
#endif

    for (size_t i = 0; i < p->cnf.clauses.size; ++i)
    {
        const Clause * cl = da_at(&p->cnf.clauses, i);
        if (cl->literals.size == 0)
        {
#ifdef DEBUG
            fprintf(stderr, "\n\tEmpty clause");
#endif
            return -1;
        }
    }

    size_t interp_len = p->interp.size;
    cnf_find_pure_literals(&p->cnf, &p->interp);
    for (size_t i = interp_len; i < p->interp.size; ++i)
    {
        int32_t literal = *(int32_t*)da_at(&p->interp, i);
        size_t j = 0;
        while (j < p->cnf.clauses.size)
        {
            Clause * cl = da_at(&p->cnf.clauses, j);
            if (cl_has_literal(cl, literal) == 1)
            {
                cl_destruct(cl);
                da_remove(&p->cnf.clauses, j);
            }
            else
            {
                ++j;
            }
        }
    }

#ifdef DEBUG
    fprintf(stderr, "\n\tAfter PLE %zu, %zu:\t", p->interp.size, p->cnf.clauses.size);
    p_print(p, stderr);
#endif

    int8_t signs[p->cnf.num_vars + 1];
    if (!p_check_interp_signs(p, signs))
    {
#ifdef DEBUG
        fprintf(stderr, "\n\tBad interp");
#endif
        return -1;
    }

    if (cnf_check_true(&p->cnf, signs))
    {
#ifdef DEBUG
        fprintf(stderr, "\n\tTrue");
#endif
        return 1;
    }

    *next_var = 0;
    for (size_t i = 1; i <= p->cnf.num_vars; ++i)
    {
        if (signs[i] == 0)
        {
            *next_var = i;
            break;
        }
    }

    if (!*next_var)
        abort();

#ifdef DEBUG
    fprintf(stderr, "\n\tNext var %d", *next_var);
#endif
    return 0;
}


bool p_dpll(Problem * p)
{
    Problem initial = p_clone(p);
    cnf_remove_tautology(&initial.cnf);

    DynArr problems_stack = da_construct_size(sizeof(Problem), initial.cnf.num_vars);
    da_push_back(&problems_stack, &initial);

    bool solved = false;
    while (problems_stack.size)
    {
        Problem p0 = *(Problem *)da_back(&problems_stack);
        da_pop_back(&problems_stack);
        int32_t next_var;
        int res = p_dpll_impl(&p0, &next_var);

        if (res == 1)
        {
            p_destruct(p);
            *p = p0;
            solved = true;
            break;
        }
        else if (res == -1)
        {
            p_destruct(&p0);
            continue;
        }

        // res == 0
        Problem p1 = p_clone(&p0);
        Clause cl_next_var;
        cl_next_var.literals = da_construct_size(sizeof(int32_t), 1);
        da_push_back(&cl_next_var.literals, &next_var);
        da_push_back(&p1.cnf.clauses, &cl_next_var);
        da_push_back(&problems_stack, &p1);

        Problem p2 = p_clone(&p0);
        cl_next_var.literals = da_construct_size(sizeof(int32_t), 1);
        next_var = -next_var;
        da_push_back(&cl_next_var.literals, &next_var);
        da_push_back(&p2.cnf.clauses, &cl_next_var);
        da_push_back(&problems_stack, &p2);

        p_destruct(&p0);
    }

    for (size_t i = 0; i < problems_stack.size; ++i)
        p_destruct(da_at(&problems_stack, i));
    da_destruct(&problems_stack);

    return solved;
}

// ============================================================================
//                                Main
// ============================================================================


int main()
{
    fputs("Usage: ./a.out < input.cnf 2>/dev/null 1>output.solution\n", stderr);
    
    Problem p = p_parse(stdin);
    bool solved = p_dpll(&p);
    if (solved)
        fputs("Solved\n", stdout);
    else
        fputs("Not solved\n", stdout);
    
    p_print(&p, stdout);
    fputc('\n', stdout);

    p_destruct(&p);
}





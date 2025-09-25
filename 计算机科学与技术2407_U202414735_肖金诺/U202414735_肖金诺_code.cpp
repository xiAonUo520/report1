#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <time.h>
#include <ctype.h>
#define MAXVAR 729
#define VAR(i,j,k)  ( ( (i)-1 )*81 + ( (j)-1 )*9 + (k) )
#define UNIT_QUEUE_MAX  (MAXVAR*2+1)
int decision_level = 0;

#define DEBUG_LEVEL 0

#if DEBUG_LEVEL > 0
#define DEBUG_PRINT(level, ...) if (DEBUG_LEVEL >= level) { printf(__VA_ARGS__); fflush(stdout); }
#else
#define DEBUG_PRINT(level, ...)
#endif
typedef struct Clause {
    int *lits;
    int size;
    bool sat;
    struct Clause *next;
    int remaining;
    int id;
} Clause;
typedef struct OccurrenceNode {
    Clause *clause;
    struct OccurrenceNode *next;
} OccurrenceNode;

typedef struct CNFClause {
    int literal_count;
    int *literals;
} CNFClause;

typedef struct CNFFormula {
    int variable_count;
    int clause_count;
    CNFClause *clauses;
} CNFFormula;

typedef struct Var {
    char value;
    bool decided;
    OccurrenceNode *pos;
    OccurrenceNode *neg;
} Var;

extern Clause *clauses;
extern Var     vars[730];
int     var_cnt;
int     assignment[730];
int decision[MAXVAR + 1];
int level = 0;
int  trail_top = 0;
int  trail[MAXVAR];
int clause_cnt = 0;
int clause_id_counter = 0;

typedef struct {
    int  v;
    int  branch;
    int  level;
} Frame;

Frame stack[MAXVAR];
int   sp = 0;
Clause *new_clause(const int *lits, int size);
Clause *insert_clause_head(Clause *head, Clause *newclause);
void add_cell_constraints(Clause **head);
void add_row_constraints(Clause **head);
void add_col_constraints(Clause **head);
void add_box_constraints(Clause **head);
void add_diagonal_constraints(Clause **head);
void add_window_constraints(Clause **head);
Clause *read_sdk_to_clauses(const char *filename);
Clause *read_cnf(const char *fname, int *var_cnt, int *clause_cnt);
void build_occurrence();
void print_conflict_clause(Clause *c);
bool unit_propagate(void);
double get_ms(void);
int pick_var_moms(void);
int pick_var(void);
bool dpll(void);
void save_assign(int v, int val);
void backtrack(int level);
void write_cnf(const char *fname, int var_cnt, Clause *clauses);
void fill_box(char grid[9][9], int row, int col);
void solve_sudoku(char grid[9][9]);
bool is_complete(char grid[9][9]);
bool is_valid(char grid[9][9]);
void play_sudoku();
void print_sudoku(char grid[9][9]);
Clause* create_sudoku_cnf(char grid[9][9]);


void save_assign(int v, int val)
{
    assignment[v]   = val;
    vars[v].decided = true;
    vars[v].value = val;
    trail[trail_top++] = v;
    DEBUG_PRINT(2, "[DEBUG] Assignment: variable %d = %d\n", v, val);
}

void backtrack(int level)
{
    DEBUG_PRINT(2, "[DEBUG] Backtracking to level %d (current level: %d)\n", level, decision_level);
    
    for (Clause *c = clauses; c; c = c->next) {
        c->sat = false;
        c->remaining = 0;
        for (int *p = c->lits; *p; ++p) {
            if (!vars[abs(*p)].decided) {
                c->remaining++;
            }
        }
    }
    
    while (trail_top > level)
    {
        --trail_top;
        int v = trail[trail_top];
        assignment[v]   = 0;
        vars[v].decided = false;
        vars[v].value   = 0;
        DEBUG_PRINT(2, "[DEBUG] Undo assignment: variable %d\n", v);
    }
}

Var vars[730]; 
Clause *clauses;

void write_cnf(const char *fname, int var_cnt, Clause *clauses)
{
    FILE *fp = fopen(fname, "w");
    if (!fp) { perror("open"); exit(EXIT_FAILURE); }

    int clause_cnt = 0;
    for (Clause *p = clauses; p; p = p->next) ++clause_cnt;
    fprintf(fp, "p cnf %d %d\n", var_cnt, clause_cnt);

    for (Clause *p = clauses; p; p = p->next) {
        for (int i = 0; i < p->size; ++i)
            fprintf(fp, "%d ", p->lits[i]);
        fprintf(fp, "0\n");
    }

    fclose(fp);
}

Clause *new_clause(const int *lits, int size)
{
    Clause *c = (Clause*)malloc(sizeof(Clause));
    c->lits = (int*)malloc((size + 1) * sizeof(int));
    for (int i = 0; i < size; ++i) c->lits[i] = lits[i];
    c->lits[size] = 0;   // End with 0
    c->size = size;
    c->next = NULL;
    c->sat = 0;
    c->id = clause_id_counter++; // Assign unique ID
    DEBUG_PRINT(3, "[DEBUG] Created new clause ID=%d: ", c->id);
    for (int i = 0; i < size; ++i) DEBUG_PRINT(3, "%d ", lits[i]);
    DEBUG_PRINT(3, "0\n");
    return c;
}

//O(1)
Clause *insert_clause_head(Clause *head, Clause *newclause)
{
    DEBUG_PRINT(3, "[DEBUG] Inserting clause ID=%d at head\n", newclause->id);
    newclause->next = head;
    return newclause;
}

void add_cell_constraints(Clause **head)
{
    DEBUG_PRINT(1, "[DEBUG] Adding cell constraints\n");
    for (int i = 1; i <= 9; ++i)
        for (int j = 1; j <= 9; ++j) {
            int at_least[9];
            for (int k = 1; k <= 9; ++k) at_least[k-1] =  VAR(i,j,k); // Each cell must have a number
            *head = insert_clause_head(*head, new_clause(at_least, 9));

            for (int k1 = 1; k1 <= 9; ++k1)
                for (int k2 = k1+1; k2 <= 9; ++k2) {
                    int lits[2] = { -VAR(i,j,k1), -VAR(i,j,k2) }; // Each cell can only have one number
                    *head = insert_clause_head(*head, new_clause(lits, 2));
                }
        }
}

void add_row_constraints(Clause **head)
{
    DEBUG_PRINT(1, "[DEBUG] Adding row constraints\n");
    for (int r = 1; r <= 9; ++r)
        for (int k = 1; k <= 9; ++k) {
            int exist[9];
            for (int c = 1; c <= 9; ++c) exist[c-1] = VAR(r,c,k); // Each row must contain each number
            *head = insert_clause_head(*head, new_clause(exist, 9));

            for (int c1 = 1; c1 <= 9; ++c1)
                for (int c2 = c1+1; c2 <= 9; ++c2) {
                    int lits[2] = { -VAR(r,c1,k), -VAR(r,c2,k) };
                    *head = insert_clause_head(*head, new_clause(lits, 2)); // Each number can appear only once per row
                }
        }
}

void add_col_constraints(Clause **head)
{
    DEBUG_PRINT(1, "[DEBUG] Adding column constraints\n");
    for (int c = 1; c <= 9; ++c)
        for (int k = 1; k <= 9; ++k) {
            int exist[9];
            for (int r = 1; r <= 9; ++r) exist[r-1] = VAR(r,c,k); // Each column must contain each number
            *head = insert_clause_head(*head, new_clause(exist, 9));

            for (int r1 = 1; r1 <= 9; ++r1)
                for (int r2 = r1+1; r2 <= 9; ++r2) {
                    int lits[2] = { -VAR(r1,c,k), -VAR(r2,c,k) };
                    *head = insert_clause_head(*head, new_clause(lits, 2)); // Each number can appear only once per column
                }
        }
}

void add_box_constraints(Clause **head)
{
    DEBUG_PRINT(1, "[DEBUG] Adding box constraints\n");
    for (int br = 0; br < 3; ++br)
        for (int bc = 0; bc < 3; ++bc)
            for (int k = 1; k <= 9; ++k) {
                int exist[9], idx = 0;
                for (int i = 1; i <= 3; ++i)
                    for (int j = 1; j <= 3; ++j)
                        exist[idx++] = VAR(br*3+i, bc*3+j, k);
                *head = insert_clause_head(*head, new_clause(exist, 9)); // Each box must contain each number

                for (int i1 = 1; i1 <= 3; ++i1)
                    for (int j1 = 1; j1 <= 3; ++j1)
                        for (int i2 = i1; i2 <= 3; ++i2)
                            for (int j2 = (i1==i2?j1+1:1); j2 <= 3; ++j2) {
                                int lits[2] = {
                                    -VAR(br*3+i1, bc*3+j1, k),
                                    -VAR(br*3+i2, bc*3+j2, k)
                                };
                                *head = insert_clause_head(*head, new_clause(lits, 2)); // Each number can appear only once per box
                            }
            }
}

void add_diagonal_constraints(Clause **head)
{
    DEBUG_PRINT(1, "[DEBUG] Adding diagonal constraints\n");
    for (int k = 1; k <= 9; ++k) {
        int exist[9];
        for (int r = 1; r <= 9; ++r)
            exist[r-1] = VAR(r, 10 - r, k);
        *head = insert_clause_head(*head, new_clause(exist, 9)); // Diagonal must contain each number

        for (int r1 = 1; r1 <= 9; ++r1)
            for (int r2 = r1 + 1; r2 <= 9; ++r2) {
                int lits[2] = {
                    -VAR(r1, 10 - r1, k),
                    -VAR(r2, 10 - r2, k)
                };
                *head = insert_clause_head(*head, new_clause(lits, 2)); // Each number can appear only once on diagonal
            }
    }
}

void add_window_constraints(Clause **head)
{
    DEBUG_PRINT(1, "[DEBUG] Adding window constraints\n");
    struct { int r0, c0; } win[2] = { {2,2}, {6,6} };

    for (int w = 0; w < 2; ++w) {
        int r0 = win[w].r0, c0 = win[w].c0;

        for (int k = 1; k <= 9; ++k) {
            int exist[9], idx = 0;
            for (int dr = 0; dr < 3; ++dr)
                for (int dc = 0; dc < 3; ++dc)
                    exist[idx++] = VAR(r0 + dr, c0 + dc, k);
            *head = insert_clause_head(*head, new_clause(exist, 9)); // Each window must contain each number

            for (int dr1 = 0; dr1 < 3; ++dr1)
                for (int dc1 = 0; dc1 < 3; ++dc1)
                    for (int dr2 = dr1; dr2 < 3; ++dr2)
                        for (int dc2 = (dr1==dr2?dc1+1:0); dc2 < 3; ++dc2) {
                            int lits[2] = {
                                -VAR(r0 + dr1, c0 + dc1, k),
                                -VAR(r0 + dr2, c0 + dc2, k)
                            };
                            *head = insert_clause_head(*head, new_clause(lits, 2)); // Each number can appear only once per window
                        }
        }
    }
}

Clause *read_sdk_to_clauses(const char *filename)
{
    DEBUG_PRINT(1, "[DEBUG] Reading Sudoku from file: %s\n", filename);
    FILE *fp = fopen(filename, "r");
    if (!fp) { perror("open sdk"); exit(EXIT_FAILURE); }

    Clause *head = NULL;
    char line[82] = { 0 };
    size_t len = fread(line, 1, 81, fp);
    if (len != 81) {
        fprintf(stderr, "sdk format error: not 81 chars\n");
        exit(EXIT_FAILURE);
    }

    for (int r = 1; r <= 9; ++r) {
    for (int c = 1; c <= 9; ++c) {
        int pos = (r - 1) * 9 + (c - 1);
        char ch = line[pos];
        if (ch >= '1' && ch <= '9') {
            int val = ch - '0';
            int lit = VAR(r, c, val);
            head = insert_clause_head(head, new_clause(&lit, 1));
            }
        }
    }
    fclose(fp);
    return head;
}

Clause *read_cnf(const char *fname, int *var_cnt, int *clause_cnt)
{
    DEBUG_PRINT(1, "[DEBUG] Reading CNF file: %s\n", fname);
    FILE *fp = fopen(fname, "r");
    if (!fp) { perror("read_cnf"); exit(EXIT_FAILURE); }

    Clause *head = NULL;
    char line[256];

    while (fgets(line, sizeof(line), fp)) {
        if (line[0] == 'c' || line[0] == '\n') continue;

        if (line[0] == 'p') {
            sscanf(line, "p cnf %d %d", var_cnt, clause_cnt);
            DEBUG_PRINT(1, "[DEBUG] CNF file info: variables=%d, clauses=%d\n", *var_cnt, *clause_cnt);
            continue;
        }

        int buf[1024], idx = 0;
        char *tok = strtok(line, " \t\n");
        while (tok) {
            int lit = atoi(tok);
            if (lit == 0) break;
            buf[idx++] = lit;
            tok = strtok(NULL, " \t\n");
        }
        if (idx) head = insert_clause_head(head, new_clause(buf, idx));
    }
    fclose(fp);
    return head;
}

void build_occurrence()
{
    DEBUG_PRINT(1, "[DEBUG] Building occurrence lists\n");
    for (int i = 1; i <= MAXVAR; ++i) {
        vars[i].pos = NULL;
        vars[i].neg = NULL;
    }
    
    int clause_count = 0;
    int literal_count = 0;
    
    Clause *c = clauses;
    while (c != NULL) {
        clause_count++;
        DEBUG_PRINT(3, "[DEBUG] Processing clause ID=%d\n", c->id);
        
        int *p = c->lits;
        while (*p != 0) {
            literal_count++;
            int v = abs(*p);
            if (v < 1 || v > MAXVAR) {
                DEBUG_PRINT(1, "[WARNING] Invalid variable number: %d\n", v);
                p++;
                continue;
            }
            
            OccurrenceNode *new_node = (OccurrenceNode*)malloc(sizeof(OccurrenceNode));
            new_node->clause = c;
            new_node->next = NULL;
            
            if (*p > 0) {
                new_node->next = vars[v].pos;
                vars[v].pos = new_node;
                DEBUG_PRINT(3, "[DEBUG] Variable %d appears in positive literal clause ID=%d\n", v, c->id);
            } else {
                new_node->next = vars[v].neg;
                vars[v].neg = new_node;
                DEBUG_PRINT(3, "[DEBUG] Variable %d appears in negative literal clause ID=%d\n", v, c->id);
            }
            
            p++;
        }
        c = c->next;
    }
    
    DEBUG_PRINT(1, "[DEBUG] Occurrence list building complete, processed %d clauses, %d literals\n", clause_count, literal_count);
}

void print_conflict_clause(Clause *c) {
    DEBUG_PRINT(1, "[CONFLICT] Conflict clause ID=%d: ", c->id);
    for (int *p = c->lits; *p; ++p) {
        int lit = *p;
        int var = abs(lit);
        DEBUG_PRINT(1, "%d(", lit);
        if (vars[var].decided) {
            DEBUG_PRINT(1, "%d", vars[var].value);
        } else {
            DEBUG_PRINT(1, "undecided");
        }
        DEBUG_PRINT(1, ") ");
    }
    DEBUG_PRINT(1, "0\n");
}

bool unit_propagate(void) {
    static char inQ[UNIT_QUEUE_MAX];
    static int queue[UNIT_QUEUE_MAX];
    memset(inQ, 0, sizeof(inQ));
    int ql = 0;
    DEBUG_PRINT(2, "[DEBUG] Starting unit propagation, recalculating clause states\n");
    
    for (Clause *c = clauses; c; c = c->next) {
        if (c->sat) continue;
        
        // Check if clause is already satisfied
        bool satisfied = false;
        for (int *p = c->lits; *p; ++p) {
            int u = *p;
            int u_var = abs(u);
            if (vars[u_var].decided && vars[u_var].value == (u > 0 ? 1 : -1)) {
                satisfied = true;
                break;
            }
        }
        if (satisfied) {
            c->sat = true;
            DEBUG_PRINT(3, "[DEBUG] Clause ID=%d is satisfied\n", c->id);
            continue;
        }

        // Count remaining undecided literals
        c->remaining = 0;
        for (int *p = c->lits; *p; ++p) {
            int u = *p;
            if (!vars[abs(u)].decided) {
                c->remaining++;
            }
        }
        
        DEBUG_PRINT(3, "[DEBUG] Clause ID=%d remaining undecided literals: %d\n", c->id, c->remaining);
        
        if (c->remaining == 0) {
            DEBUG_PRINT(1, "[CONFLICT] Clause ID=%d has no remaining undecided literals and is unsatisfied\n", c->id);
            print_conflict_clause(c);
            return false; // Conflict: clause is unsatisfied
        }
        
        if (c->remaining == 1) {
            // Find undecided literal and add to queue
            for (int *p = c->lits; *p; ++p) {
                int u = *p;
                if (!vars[abs(u)].decided) {
                    if (!inQ[u + MAXVAR]) {
                        inQ[u + MAXVAR] = 1;
                        queue[ql++] = u;
                        DEBUG_PRINT(2, "[DEBUG] Added unit literal to queue: %d (from clause ID=%d)\n", u, c->id);
                    }
                    break;
                }
            }
        }
    }

    // Process queue of unit literals
    while (ql > 0) {
        int lit = queue[--ql];
        DEBUG_PRINT(2, "[DEBUG] Processing unit literal: %d\n", lit);
        inQ[lit + MAXVAR] = 0;

        int v = abs(lit);
        int val = lit > 0 ? 1 : -1;

        if (vars[v].decided) {
            if (vars[v].value != val) {
                DEBUG_PRINT(1, "[CONFLICT] Unit literal %d conflicts with existing assignment\n", lit);
                return false;
            }
            continue;
        }

        // Assign value
        vars[v].value = val;
        vars[v].decided = true;
        assignment[v] = val;
        trail[trail_top++] = v;
        DEBUG_PRINT(2, "[DEBUG] Unit propagation assignment: variable %d = %d\n", v, val);

        // Process positive occurrence list
        OccurrenceNode *list_pos = vars[v].pos;
        for (OccurrenceNode *node = list_pos; node; node = node->next){
            Clause *c = node->clause;
            if (c->sat) continue;
            if (val == 1) {
                c->sat = true;
                DEBUG_PRINT(3, "[DEBUG] Clause ID=%d satisfied because variable %d=1\n", c->id, v);
                continue;
            }
            c->remaining--;
            DEBUG_PRINT(3, "[DEBUG] Clause ID=%d remaining undecided literals reduced to: %d\n", c->id, c->remaining);
            
            if (c->remaining == 0) {
                // Check if clause is really unsatisfied
                bool satisfied = false;
                for (int *p = c->lits; *p; ++p) {
                    int u = *p;
                    int u_var = abs(u);
                    if (vars[u_var].decided && vars[u_var].value == (u > 0 ? 1 : -1)) {
                        satisfied = true;
                        break;
                    }
                }
                if (!satisfied) {
                    DEBUG_PRINT(1, "[CONFLICT] Clause ID=%d has no remaining undecided literals and is unsatisfied\n", c->id);
                    print_conflict_clause(c);
                    return false; // Conflict
                } else {
                    c->sat = true; // Mark as satisfied
                    DEBUG_PRINT(3, "[DEBUG] Clause ID=%d is satisfied\n", c->id);
                }
            }
            
            if (c->remaining == 1) {
                // Find undecided literal and add to queue
                for (int *p = c->lits; *p; ++p) {
                    int u = *p;
                    if (!vars[abs(u)].decided) {
                        if (!inQ[u + MAXVAR]) {
                            inQ[u + MAXVAR] = 1;
                            queue[ql++] = u;
                            DEBUG_PRINT(2, "[DEBUG] Added new unit literal to queue: %d (from clause ID=%d)\n", u, c->id);
                        }
                        break;
                    }
                }
            }
        }

        // Process negative occurrence list
        OccurrenceNode *list_neg = vars[v].neg;
        for (OccurrenceNode *node = list_neg; node; node = node->next) {
            Clause *c = node->clause;
            if (c->sat) continue;
            if (val == -1) {
                // Clause is satisfied because v is false
                c->sat = true;
                DEBUG_PRINT(3, "[DEBUG] Clause ID=%d satisfied because variable %d=-1\n", c->id, v);
                continue;
            }
            // v is true, reduce remaining count
            c->remaining--;
            DEBUG_PRINT(3, "[DEBUG] Clause ID=%d remaining undecided literals reduced to: %d\n", c->id, c->remaining);
            
            if (c->remaining == 0) {
                // Check if clause is really unsatisfied
                bool satisfied = false;
                for (int *p = c->lits; *p; ++p) {
                    int u = *p;
                    int u_var = abs(u);
                    if (vars[u_var].decided && vars[u_var].value == (u > 0 ? 1 : -1)) {
                        satisfied = true;
                        break;
                    }
                }
                if (!satisfied) {
                    DEBUG_PRINT(1, "[CONFLICT] Clause ID=%d has no remaining undecided literals and is unsatisfied\n", c->id);
                    print_conflict_clause(c);
                    return false; // Conflict
                } else {
                    c->sat = true; // Mark as satisfied
                    DEBUG_PRINT(3, "[DEBUG] Clause ID=%d is satisfied\n", c->id);
                }
            }
            
            if (c->remaining == 1) {
                // Find undecided literal and add to queue
                for (int *p = c->lits; *p; ++p) {
                    int u = *p;
                    if (!vars[abs(u)].decided) {
                        if (!inQ[u + MAXVAR]) {
                            inQ[u + MAXVAR] = 1;
                            queue[ql++] = u;
                            DEBUG_PRINT(2, "[DEBUG] Added new unit literal to queue: %d (from clause ID=%d)\n", u, c->id);
                        }
                        break;
                    }
                }
            }
        }
    }
    
    DEBUG_PRINT(2, "[DEBUG] Unit propagation completed\n");
    return true;
}

double get_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1e6;
}

int pick_var_moms(void) {
    DEBUG_PRINT(2, "[DEBUG] Using MOMS heuristic to select variable\n");
    int maxcnt = -1, bestv = 0;
    for (int v = 1; v <= var_cnt; ++v) {
        if (assignment[v]) continue; // Skip assigned variables
        int cnt = 0;
        // 遍历正文字出现列表
        for (OccurrenceNode *node = vars[v].pos; node; node = node->next) {
            Clause *c = node->clause;
            if (c->remaining == 2) cnt++;
        }
        // 遍历负文字出现列表
        for (OccurrenceNode *node = vars[v].neg; node; node = node->next) {
            Clause *c = node->clause;
            if (c->remaining == 2) cnt++;
        }
        if (cnt > maxcnt) {
            maxcnt = cnt;
            bestv = v;
        }
    }
    if (bestv != 0) {
        DEBUG_PRINT(2, "[DEBUG] MOMS selected variable: %d (count: %d\n", bestv, maxcnt);
        return bestv;
    }
    // Fallback: select first unassigned variable
    DEBUG_PRINT(2, "[DEBUG] MOMS found no variable, using first unassigned variable\n");
    for (int v = 1; v <= var_cnt; ++v) {
        if (assignment[v] == 0) return v;
    }
    return 0; // All variables assigned
}

int pick_var(void)
{
    DEBUG_PRINT(2, "[DEBUG] Selecting first unassigned variable\n");
    for (int v = 1; v <= var_cnt; ++v)
        if (assignment[v] == 0) return v;
    return 0;
}

bool dpll(void)
{
    static Frame stack[MAXVAR];
    int sp = 0;
    int decision_level = 0;

    DEBUG_PRINT(1, "[DEBUG] Starting DPLL algorithm\n");
    
    while(1)
    {
        DEBUG_PRINT(2, "[DEBUG] Calling unit propagation at level %d\n", decision_level);
        
        // 单元传播
        bool propagation_success = unit_propagate();
        if (!propagation_success) {
            DEBUG_PRINT(1, "[CONFLICT] Conflict detected at level %d\n", decision_level);
            
            // 回溯处理
            bool should_continue = false;
            while (sp > 0 && !should_continue)
            {
                --sp;
                int v = stack[sp].v;
                int branch = stack[sp].branch;
                
                if (branch == 1) {
                    stack[sp].branch = -1;
                    int lvl = stack[sp].level;
                    backtrack(lvl);
                    decision_level = lvl;
                    
                    DEBUG_PRINT(1, "[DECISION] Trying variable %d to false at level %d\n", v, decision_level);
                    save_assign(v, -1);
                    ++decision_level;
                    
                    if (unit_propagate()) {
                        should_continue = true;
                        DEBUG_PRINT(1, "[DEBUG] Unit propagation after backtrack successful, continuing\n");
                    } else {
                        DEBUG_PRINT(1, "[DEBUG] Unit propagation after backtrack failed, continuing backtrack\n");
                    }
                } else {
                    DEBUG_PRINT(1, "[BACKTRACK] Both branches tried for variable %d, backtracking further\n", v);
                    backtrack(stack[sp].level);
                    decision_level = stack[sp].level;
                }
            }
            
            if (!should_continue) {
                if (sp == 0) { 
                    decision_level = 0; 
                    DEBUG_PRINT(1, "[DEBUG] Stack empty, returning false\n");
                    return false; 
                }
                continue;
            }
        }

        // 选择变量
        int v = pick_var_moms();
        if (v == 0) { 
            --decision_level; 
            DEBUG_PRINT(1, "[DEBUG] All variables assigned, returning true\n");
            return true; 
        }

        DEBUG_PRINT(1, "[DECISION] Choosing variable %d at level %d, assigning true first\n", v, decision_level);
        stack[sp].v      = v;
        stack[sp].branch = 1;
        stack[sp].level  = decision_level;
        ++sp;
        ++decision_level;
        save_assign(v, 1);
    }
}
void fill_box(char grid[9][9], int row, int col) {
    int nums[9] = {1, 2, 3, 4, 5, 6, 7, 8, 9};
    
    // 随机打乱数字
    for (int i = 0; i < 9; i++) {
        int j = rand() % 9;
        int temp = nums[i];
        nums[i] = nums[j];
        nums[j] = temp;
    }
    
    // 填充宫格
    int index = 0;
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            grid[row + i][col + j] = nums[index++];
        }
    }
}

// 生成百分号数独游戏
void generate_percent_sudoku(char grid[9][9], int difficulty) {
    // 初始化网格为全0
    memset(grid, 0, sizeof(char) * 81);
    
    // 首先创建一个完整的合法数独
    // 这是一个简化版本，实际应用中可能需要更复杂的算法
    
    // 填充对角线上的3x3宫格
    for (int i = 0; i < 9; i += 3) {
        fill_box(grid, i, i);
    }
    
    // 尝试填充剩余部分
    solve_sudoku(grid); // 使用SAT求解器填充完整
    
    // 根据难度挖空
    int holes = difficulty; // 难度决定挖空数量
    srand(time(NULL));
    
    while (holes > 0) {
        int r = rand() % 9;
        int c = rand() % 9;
        
        if (grid[r][c] != 0) {
            grid[r][c] = 0;
            holes--;
        }
    }
}
Clause* create_sudoku_cnf(char grid[9][9]) {
    Clause* head = NULL;
    
    // 添加基本约束
    add_cell_constraints(&head);
    add_row_constraints(&head);
    add_col_constraints(&head);
    add_box_constraints(&head);
    
    // 添加百分号数独的特殊约束
    add_diagonal_constraints(&head);
    add_window_constraints(&head);
    
    // 添加已知数字的约束
    for (int i = 0; i < 9; i++) {
        for (int j = 0; j < 9; j++) {
            if (grid[i][j] != 0) {
                int k = grid[i][j];
                int lit = VAR(i+1, j+1, k);
                head = insert_clause_head(head, new_clause(&lit, 1));
            }
        }
    }
    
    return head;
}
// 使用SAT求解器解决数独
void solve_sudoku(char grid[9][9]) {
    // 创建数独的CNF公式
    Clause* sudoku_clauses = create_sudoku_cnf(grid);
    
    // 保存原始子句列表
    Clause* original_clauses = clauses;
    
    // 设置新的子句列表
    clauses = sudoku_clauses;
    
    // 重置变量状态
    trail_top = 0;
    sp        = 0;
    for (int i = 0; i <= MAXVAR; ++i){
        vars[i].pos = vars[i].neg = NULL;
        vars[i].decided = false;
        vars[i].value   = 0;
    }
    build_occurrence();
    for (Clause *c = clauses; c; c = c->next) {
        c->sat = false;
        c->remaining = 0;
        for (int *p = c->lits; *p; ++p) {
            if (!vars[abs(*p)].decided) {
                c->remaining++;
            }
        }
    }
    bool solved = dpll();
    
    
    if (solved) {
        // 从赋值中提取数独解
        for (int i = 1; i <= 9; i++) {
            for (int j = 1; j <= 9; j++) {
                for (int k = 1; k <= 9; k++) {
                    int var = VAR(i, j, k);
                    if (vars[var].value > 0) {
                        grid[i-1][j-1] = k;
                        break;
                    }
                }
            }
        }
    } else {
        printf("Failed to solve the Sudoku!\n");
    }
    
    // 恢复原始子句列表
    clauses = original_clauses;
    
    // 释放数独子句内存
    Clause* current = sudoku_clauses;
    while (current) {
        Clause* next = current->next;
        free(current->lits);
        free(current);
        current = next;
    }
}

// 检查数独是否已完成
bool is_complete(char grid[9][9]) {
    for (int i = 0; i < 9; i++) {
        for (int j = 0; j < 9; j++) {
            if (grid[i][j] == 0) {
                return false;
            }
        }
    }
    return true;
}

// 检查数独是否有效
bool is_valid(char grid[9][9]) {
    // 检查行
    for (int i = 0; i < 9; i++) {
        bool seen[10] = {false};
        for (int j = 0; j < 9; j++) {
            int num = grid[i][j];
            if (num != 0 && seen[num]) {
                return false;
            }
            seen[num] = true;
        }
    }
    
    // 检查列
    for (int j = 0; j < 9; j++) {
        bool seen[10] = {false};
        for (int i = 0; i < 9; i++) {
            int num = grid[i][j];
            if (num != 0 && seen[num]) {
                return false;
            }
            seen[num] = true;
        }
    }
    
    // 检查宫格
    for (int box = 0; box < 9; box++) {
        bool seen[10] = {false};
        int startRow = (box / 3) * 3;
        int startCol = (box % 3) * 3;
        
        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 3; j++) {
                int num = grid[startRow + i][startCol + j];
                if (num != 0 && seen[num]) {
                    return false;
                }
                seen[num] = true;
            }
        }
    }
    
    // 检查对角线
    bool seen1[10] = {false};
    bool seen2[10] = {false};
    for (int i = 0; i < 9; i++) {
        int num1 = grid[i][i];
        int num2 = grid[i][8 - i];
        
        if (num1 != 0 && seen1[num1]) {
            return false;
        }
        if (num2 != 0 && seen2[num2]) {
            return false;
        }
        
        seen1[num1] = true;
        seen2[num2] = true;
    }
    
    // 检查窗口
    int windows[2][2] = {{1, 1}, {5, 5}}; // 窗口的起始位置
    
    for (int w = 0; w < 2; w++) {
        bool seen[10] = {false};
        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 3; j++) {
                int num = grid[windows[w][0] + i][windows[w][1] + j];
                if (num != 0 && seen[num]) {
                    return false;
                }
                seen[num] = true;
            }
        }
    }
    
    return true;
}

// 打印数独网格
void print_sudoku(char grid[9][9]) {
    printf("+-------+-------+-------+\n");
    for (int i = 0; i < 9; i++) {
        printf("| ");
        for (int j = 0; j < 9; j++) {
            if (grid[i][j] == 0) {
                printf(". ");
            } else {
                printf("%d ", grid[i][j]);
            }
            
            if ((j + 1) % 3 == 0) {
                printf("| ");
            }
        }
        printf("\n");
        
        if ((i + 1) % 3 == 0) {
            printf("+-------+-------+-------+\n");
        }
    }
}

// 玩数独游戏
void play_sudoku() {
    char grid[9][9];
    
    // 生成数独
    generate_percent_sudoku(grid, 30); // 30个空格
    
    printf("Welcome to Percent Sudoku Game!\n");
    printf("Rules:\n");
    printf("1. Each row, column, and 3x3 box must contain numbers 1-9\n");
    printf("2. The two diagonals must also contain numbers 1-9\n");
    printf("3. The two window areas (top-left and bottom-right) must also contain numbers 1-9\n");
    printf("Input format: row column value (e.g., 1 2 3 means row 1, column 2, value 3)\n");
    printf("Enter 0 0 0 to solve the Sudoku\n\n");
    
    while (1) {
        print_sudoku(grid);
        
        int r, c, v;
        printf("Please enter row, column and value: ");
        scanf("%d %d %d", &r, &c, &v);
        
        if (r == 0 && c == 0 && v == 0) {
            printf("Solving...\n");
            solve_sudoku(grid);
            print_sudoku(grid);
            printf("Game over!\n");
            break;
        }
        
        if (r < 1 || r > 9 || c < 1 || c > 9 || v < 1 || v > 9) {
            printf("Invalid input! Row and column must be between 1-9, value must be between 1-9.\n");
            continue;
        }
        
        grid[r-1][c-1] = v;
        
        // 检查是否完成
        if (is_complete(grid)) {
            if (is_valid(grid)) {
                print_sudoku(grid);
                printf("Congratulations! You solved the Sudoku!\n");
                break;
            } else {
                printf("Sorry, the solution is incorrect. Please try again.\n");
            }
        }
    }
}




static void trim_path(char *s)
{
    int n = (int)strlen(s);
    while (n > 0 && (s[n - 1] == '\n' || s[n - 1] == '\r' || isspace((unsigned char)s[n - 1])))
        s[--n] = '\0';
    int i = 0;
    while (s[i] && isspace((unsigned char)s[i]))
        i++;
    if (i > 0)
        memmove(s, s + i, strlen(s + i) + 1);
    n = (int)strlen(s);
    if (n >= 2 && ((s[0] == '\"' && s[n - 1] == '\"') || (s[0] == '\'' && s[n - 1] == '\'')))
    {
        s[n - 1] = '\0';
        memmove(s, s + 1, strlen(s));
    }
}

/* 读取 9 行棋盘，'.' 或 '0' 为空，其余 1..9 */
static void read_grid_from_stdin(char grid[9][9])
{
    char buf[256];
    int r, c;
    for (r = 0; r < 9; r++)
    {
        if (!fgets(buf, sizeof(buf), stdin)) {
            printf("读取第 %d 行失败\n", r + 1);
            return;
        }
        int k = 0;
        for (c = 0; c < 9; c++)
        {
            while (buf[k] && isspace((unsigned char)buf[k]))
                k++;
            if (!buf[k])
            {
                grid[r][c] = 0;
                continue;
            }
            char ch = buf[k++];
            if (ch == '.' || ch == '0')
                grid[r][c] = 0;
            else if (ch >= '1' && ch <= '9')
                grid[r][c] = ch - '0';
            else
            {
                grid[r][c] = 0;
            }
        }
    }
}

static void cnf_mode()
{
    char path[1024];
    printf("输入 CNF 文件路径: ");
    if (!fgets(path, sizeof(path), stdin))
        return;
    trim_path(path);

    if (strlen(path) == 0) {
        printf("文件路径不能为空\n");
        return;
    }

    char output_path[1024];
    strcpy(output_path, path);
    char *dot = strrchr(output_path, '.');
    if (dot) {
        strcpy(dot, ".res");
    } else {
        strcat(output_path, ".res");
    }

    // 初始化变量
    DEBUG_PRINT(0, "=== 开始CNF求解 ===\n");
    trail_top = 0;
    sp = 0;
    for (int i = 0; i <= MAXVAR; ++i){
        vars[i].pos = vars[i].neg = NULL;
        vars[i].decided = false;
        vars[i].value = 0;
    }
    
    // 读取CNF文件
    int var_cnt, clause_cnt;
    clauses = read_cnf(path, &var_cnt, &clause_cnt);
    if (clauses == NULL) {
        printf("无法读取CNF文件: %s\n", path);
        return;
    }
    
    build_occurrence();
    for (Clause *c = clauses; c; c = c->next) {
        c->sat = false;
        c->remaining = 0;
        for (int *p = c->lits; *p; ++p) {
            if (!vars[abs(*p)].decided) {
                c->remaining++;
            }
        }
    }
    
    // 求解
    double start_time = get_ms();
    bool ok = dpll();
    double end_time = get_ms();
    long long elapsed_time = (long long)(end_time - start_time);
    
    // 输出结果
    FILE *fp = fopen(output_path, "w");
    if (fp == NULL) {
        printf("无法创建输出文件: %s\n", output_path);
        
        // 释放内存
        Clause *current = clauses;
        while (current) {
            Clause *next = current->next;
            free(current->lits);
            free(current);
            current = next;
        }
        return;
    }
    
    if (ok) {
        fprintf(fp, "s 1\n");
        fprintf(fp, "v ");
        for (int i = 1; i <= var_cnt; i++) {
            fprintf(fp, "%s%d ", vars[i].value > 0 ? "" : "-", i);
        }
        fprintf(fp, "\n");
        printf("求解成功！结果已保存到: %s\n", output_path);
    } else {
        fprintf(fp, "s 0\n");
        printf("问题无解！结果已保存到: %s\n", output_path);
    }
    
    fprintf(fp, "t %lldms\n", elapsed_time);
    fclose(fp);
    
    // 释放内存
    Clause *current = clauses;
    while (current) {
        Clause *next = current->next;
        free(current->lits);
        free(current);
        current = next;
    }
    
    // 释放出现列表
    for (int i = 1; i <= MAXVAR; i++) {
        OccurrenceNode *node = vars[i].pos;
        while (node) {
            OccurrenceNode *next = node->next;
            free(node);
            node = next;
        }
        
        node = vars[i].neg;
        while (node) {
            OccurrenceNode *next = node->next;
            free(node);
            node = next;
        }
    }
    
    DEBUG_PRINT(0, "=== CNF求解完成 ===\n");
}

static void export_to_cnf(char grid[9][9])
{
    Clause* sudoku_clauses = create_sudoku_cnf(grid);
    
    FILE *fp = fopen("sudoku.cnf", "w");
    if (!fp) {
        printf("无法创建文件 sudoku.cnf\n");
        return;
    }
    
    int var_count = MAXVAR;
    int clause_count = 0;
    for (Clause *c = sudoku_clauses; c; c = c->next) clause_count++;
    
    fprintf(fp, "p cnf %d %d\n", var_count, clause_count);
    
    for (Clause *c = sudoku_clauses; c; c = c->next) {
        for (int i = 0; i < c->size; i++) {
            fprintf(fp, "%d ", c->lits[i]);
        }
        fprintf(fp, "0\n");
    }
    
    fclose(fp);
    printf("已导出数独为 CNF 格式: sudoku.cnf\n");
    
    // 释放内存
    Clause *current = sudoku_clauses;
    while (current) {
        Clause *next = current->next;
        free(current->lits);
        free(current);
        current = next;
    }
}

static int input_answer(char grid[9][9], char solution[9][9])
{
    char temp[9][9];
    memcpy(temp, grid, sizeof(temp));
    
    printf("请输入完整答案（9行，每行9个数字）:\n");
    read_grid_from_stdin(temp);
    
    // 检查答案是否正确
    for (int i = 0; i < 9; i++) {
        for (int j = 0; j < 9; j++) {
            if (temp[i][j] != solution[i][j]) {
                return 0; // 答案错误
            }
        }
    }
    
    memcpy(grid, temp, sizeof(temp));
    return 1; // 答案正确
}

static void sudoku_mode()
{
    char grid[9][9] = {0};
    char solution[9][9] = {0};
    int choice, holes, symmetry;
    
    while (1)
    {
        printf("\n1. 生成题面\n");
        printf("2. 输入题面\n");
        printf("3. 求解题面\n");
        printf("4. 导出CNF\n");
        printf("5. 打印当前棋盘\n");
        printf("6. 输入答案\n");
        printf("0. 返回主菜单\n");
        printf("请选择: ");
        
        if (scanf("%d", &choice) != 1)
        {
            while (getchar() != '\n');
            continue;
        }
        while (getchar() != '\n');
        
        if (choice == 0)
            break;
        else if (choice == 5)
        {
            print_sudoku(grid);
        }
        else if (choice == 4)
        {
            export_to_cnf(grid);
        }
        else if (choice == 6)
        {
            if (is_complete(grid)) {
                printf("棋盘已完整，无需输入答案\n");
                continue;
            }
            
            if (input_answer(grid, solution)) {
                printf("答案正确！\n");
                print_sudoku(grid);
            } else {
                printf("答案错误，请重试\n");
            }
        }
        else if (choice == 3)
        {
            if (is_complete(grid)) {
                printf("棋盘已完整\n");
                continue;
            }
            
            char temp[9][9];
            memcpy(temp, grid, sizeof(temp));
            
            solve_sudoku(temp);
            
            if (is_complete(temp) && is_valid(temp)) {
                memcpy(solution, temp, sizeof(solution));
                printf("求解成功：\n");
                print_sudoku(temp);
            } else {
                printf("无解或求解失败\n");
            }
        }
        else if (choice == 2)
        {
            memset(grid, 0, sizeof(grid));
            printf("请输入 9 行(每行 9 个字符，'.' 或 '0' 为空，1..9 为数字):\n");
            read_grid_from_stdin(grid);
            printf("输入的棋盘：\n");
            print_sudoku(grid);
        }
        else if (choice == 1)
        {
            printf("目标空格数(建议 30~50): ");
            if (scanf("%d", &holes) != 1)
            {
                while (getchar() != '\n');
                continue;
            }
            while (getchar() != '\n');
            
            printf("中心对称(1=是,0=否): ");
            if (scanf("%d", &symmetry) != 1)
            {
                while (getchar() != '\n');
                continue;
            }
            while (getchar() != '\n');
            
            // 简化版的生成函数，实际应用中需要更复杂的算法
            generate_percent_sudoku(grid, holes);
            printf("生成的棋盘：\n");
            print_sudoku(grid);
        }
        else
        {
            printf("无效选择\n");
        }
    }
}


// 辅助函数：跳过注释行
void skip_comments(FILE *fp)
{
    int ch;
    while (1) {
        ch = fgetc(fp);
        if (ch == EOF) return;
        if (ch == 'c') {
            while (ch != '\n' && ch != EOF) {
                ch = fgetc(fp);
            }
        } else {
            ungetc(ch, fp);
            return;
        }
    }
}

// 辅助函数：读取下一个整数
int read_next_integer(FILE *fp, int *result)
{
    int ch;
    int sign = 1;
    
    ch = fgetc(fp);
    while (isspace(ch)) {
        ch = fgetc(fp);
        if (ch == EOF) return 0;
    }
    
    if (ch == '-') {
        sign = -1;
        ch = fgetc(fp);
    }
    
    int value = 0;
    while (isdigit(ch)) {
        value = value * 10 + (ch - '0');
        ch = fgetc(fp);
    }
    
    if (ch != EOF) ungetc(ch, fp);
    
    *result = value * sign;
    return 1;
}

// 解析CNF文件
bool parse_cnf_file(FILE *fp, CNFFormula *formula)
{
    memset(formula, 0, sizeof(*formula));
    
    skip_comments(fp);
    
    if (fscanf(fp, " p cnf %d %d", &formula->variable_count, &formula->clause_count) != 2) {
        DEBUG_PRINT(1, "[ERROR] Failed to read CNF header\n");
        return false;
    }
    
    formula->clauses = (CNFClause *)malloc(formula->clause_count * sizeof(CNFClause));
    if (!formula->clauses) {
        DEBUG_PRINT(1, "[ERROR] Memory allocation failed for clauses\n");
        return false;
    }
    
    for (int i = 0; i < formula->clause_count; i++) {
        formula->clauses[i].literals = NULL;
        formula->clauses[i].literal_count = 0;
        
        int buffer_size = 10;
        int *temp_buffer = (int *)malloc(sizeof(int) * buffer_size);
        if (!temp_buffer) {
            DEBUG_PRINT(1, "[ERROR] Memory allocation failed for temp buffer\n");
            return false;
        }
        
        int literal;
        int count = 0;
        
        while (1) {
            if (!read_next_integer(fp, &literal)) {
                free(temp_buffer);
                return false;
            }
            
            if (literal == 0) break;
            
            if (count >= buffer_size) {
                buffer_size *= 2;
                temp_buffer = (int *)realloc(temp_buffer, sizeof(int) * buffer_size);
                if (!temp_buffer) {
                    DEBUG_PRINT(1, "[ERROR] Memory reallocation failed\n");
                    return false;
                }
            }
            
            temp_buffer[count++] = literal;
        }
        
        formula->clauses[i].literal_count = count;
        formula->clauses[i].literals = (int *)malloc(count * sizeof(int));
        if (!formula->clauses[i].literals) {
            free(temp_buffer);
            DEBUG_PRINT(1, "[ERROR] Memory allocation failed for clause literals\n");
            return false;
        }
        
        for (int j = 0; j < count; j++) {
            formula->clauses[i].literals[j] = temp_buffer[j];
        }
        
        free(temp_buffer);
    }
    
    DEBUG_PRINT(1, "[INFO] Successfully parsed CNF: %d variables, %d clauses\n", 
                formula->variable_count, formula->clause_count);
    return true;
}

// 释放CNF公式内存
void free_cnf_formula(CNFFormula *formula)
{
    if (!formula || !formula->clauses) return;
    
    for (int i = 0; i < formula->clause_count; i++) {
        free(formula->clauses[i].literals);
    }
    free(formula->clauses);
}

// 打印CNF公式（调试用）
void print_cnf_formula(CNFFormula *formula)
{
    printf("CNF Formula: %d variables, %d clauses\n", formula->variable_count, formula->clause_count);
    for (int i = 0; i < formula->clause_count; i++) {
        printf("Clause %d: ", i + 1);
        for (int j = 0; j < formula->clauses[i].literal_count; j++) {
            printf("%d ", formula->clauses[i].literals[j]);
        }
        printf("0\n");
    }
}

// 文字求值函数
int evaluate_literal(int literal, const signed char *assignment)
{
    int variable = (literal > 0) ? literal : -literal;
    int value = assignment[variable];
    
    if (value == -1) return -1; // 未赋值
    return (literal > 0) ? value : (1 - value);
}

// 检查公式是否满足
bool is_formula_satisfied(const CNFFormula *formula, const signed char *assignment)
{
    for (int i = 0; i < formula->clause_count; i++) {
        bool clause_satisfied = false;
        
        for (int j = 0; j < formula->clauses[i].literal_count; j++) {
            if (evaluate_literal(formula->clauses[i].literals[j], assignment) == 1) {
                clause_satisfied = true;
                break;
            }
        }
        
        if (!clause_satisfied) {
            DEBUG_PRINT(2, "[DEBUG] Clause %d is unsatisfied\n", i + 1);
            return false;
        }
    }
    
    return true;
}

// 单元传播实现
bool perform_unit_propagation(const CNFFormula *formula, signed char *assignment, 
                             int *trail, int *trail_size)
{
    bool changed;
    
    do {
        changed = false;
        
        for (int i = 0; i < formula->clause_count; i++) {
            int unassigned_count = 0;
            int last_unassigned_literal = 0;
            bool clause_satisfied = false;
            
            for (int j = 0; j < formula->clauses[i].literal_count; j++) {
                int literal = formula->clauses[i].literals[j];
                int eval_result = evaluate_literal(literal, assignment);
                
                if (eval_result == 1) {
                    clause_satisfied = true;
                    break;
                } else if (eval_result == -1) {
                    unassigned_count++;
                    last_unassigned_literal = literal;
                }
            }
            
            if (clause_satisfied) continue;
            
            if (unassigned_count == 0) {
                DEBUG_PRINT(1, "[CONFLICT] Empty clause detected\n");
                return false;
            }
            
            if (unassigned_count == 1) {
                int variable = (last_unassigned_literal > 0) ? last_unassigned_literal : -last_unassigned_literal;
                int required_value = (last_unassigned_literal > 0) ? 1 : 0;
                
                assignment[variable] = required_value;
                trail[(*trail_size)++] = (last_unassigned_literal > 0) ? variable : -variable;
                changed = true;
                
                DEBUG_PRINT(2, "[UNIT] Variable %d assigned to %d\n", variable, required_value);
            }
        }
    } while (changed);
    
    return true;
}

// 选择未赋值的变量
int select_unassigned_variable(const signed char *assignment, int variable_count)
{
    for (int i = 1; i <= variable_count; i++) {
        if (assignment[i] == -1) {
            return i;
        }
    }
    return 0;
}

// 回溯到指定层级
void backtrack_assignment(signed char *assignment, int *trail, int *trail_size, int target_size)
{
    while (*trail_size > target_size) {
        int literal = trail[--(*trail_size)];
        int variable = (literal > 0) ? literal : -literal;
        assignment[variable] = -1;
        
        DEBUG_PRINT(2, "[BACKTRACK] Unassigned variable %d\n", variable);
    }
}

// 递归DPLL算法
bool recursive_dpll(const CNFFormula *formula, signed char *assignment, 
                    int *trail, int *trail_size)
{
    if (!perform_unit_propagation(formula, assignment, trail, trail_size)) {
        return false;
    }
    
    if (is_formula_satisfied(formula, assignment)) {
        return true;
    }
    
    int variable = select_unassigned_variable(assignment, formula->variable_count);
    if (variable == 0) return false;
    
    int saved_trail_size = *trail_size;
    
    // 尝试赋值为真
    assignment[variable] = 1;
    trail[(*trail_size)++] = variable;
    DEBUG_PRINT(2, "[DECISION] Trying variable %d = true\n", variable);
    
    if (recursive_dpll(formula, assignment, trail, trail_size)) {
        return true;
    }
    
    backtrack_assignment(assignment, trail, trail_size, saved_trail_size);
    
    // 尝试赋值为假
    assignment[variable] = 0;
    trail[(*trail_size)++] = -variable;
    DEBUG_PRINT(2, "[DECISION] Trying variable %d = false\n", variable);
    
    if (recursive_dpll(formula, assignment, trail, trail_size)) {
        return true;
    }
    
    backtrack_assignment(assignment, trail, trail_size, saved_trail_size);
    
    return false;
}

// 验证解的正确性
bool verify_solution(const CNFFormula *formula, const signed char *assignment)
{
    for (int i = 0; i < formula->clause_count; i++) {
        bool satisfied = false;
        
        for (int j = 0; j < formula->clauses[i].literal_count; j++) {
            if (evaluate_literal(formula->clauses[i].literals[j], assignment) == 1) {
                satisfied = true;
                break;
            }
        }
        
        if (!satisfied) {
            DEBUG_PRINT(1, "[VERIFY] Clause %d is not satisfied: ", i + 1);
            for (int j = 0; j < formula->clauses[i].literal_count; j++) {
                DEBUG_PRINT(1, "%d ", formula->clauses[i].literals[j]);
            }
            DEBUG_PRINT(1, "0\n");
            return false;
        }
    }
    
    DEBUG_PRINT(1, "[VERIFY] All clauses satisfied\n");
    return true;
}

// 获取当前时间（毫秒）
long long get_current_time_ms()
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

// 生成结果文件名
void generate_result_filename(const char *cnf_filename, char *result_filename)
{
    strcpy(result_filename, cnf_filename);
    char *dot = strrchr(result_filename, '.');
    if (dot) {
        strcpy(dot, ".res");
    } else {
        strcat(result_filename, ".res");
    }
}

// 主求解函数
bool solve_cnf_with_dpll(const CNFFormula *formula, const char *cnf_filename)
{
    int variable_count = formula->variable_count;
    signed char *assignment = (signed char *)malloc((variable_count + 1) * sizeof(signed char));
    int *trail = (int *)malloc((variable_count + 1) * sizeof(int));
    int trail_size = 0;
    
    // 初始化赋值数组
    for (int i = 1; i <= variable_count; i++) {
        assignment[i] = -1; // -1表示未赋值
    }
    
    // 生成结果文件名
    char result_filename[256];
    generate_result_filename(cnf_filename, result_filename);
    
    FILE *result_file = fopen(result_filename, "w");
    if (!result_file) {
        DEBUG_PRINT(1, "[ERROR] Cannot open result file: %s\n", result_filename);
        free(assignment);
        free(trail);
        return false;
    }
    
    long long start_time = get_current_time_ms();
    bool satisfiable = recursive_dpll(formula, assignment, trail, &trail_size);
    long long end_time = get_current_time_ms();
    double solving_time = (end_time - start_time) / 1000.0;
    
    if (satisfiable) {
        fprintf(result_file, "s 1\nv ");
        for (int i = 1; i <= variable_count; i++) {
            int value = (assignment[i] == -1) ? 1 : assignment[i]; // 未赋值的变量默认设为真
            fprintf(result_file, "%s%d ", (value == 1) ? "" : "-", i);
        }
        fprintf(result_file, "0\n");
        fprintf(result_file, "t %.3f\n", solving_time);
        
        DEBUG_PRINT(1, "[RESULT] SATISFIABLE\n");
        
        // 验证解
        if (verify_solution(formula, assignment)) {
            DEBUG_PRINT(1, "[VERIFY] Solution verified\n");
        } else {
            DEBUG_PRINT(1, "[VERIFY] Solution verification failed\n");
        }
    } else {
        fprintf(result_file, "s 0\n");
        fprintf(result_file, "t %.3f\n", solving_time);
        DEBUG_PRINT(1, "[RESULT] UNSATISFIABLE\n");
    }
    
    fclose(result_file);
    free(assignment);
    free(trail);
    
    DEBUG_PRINT(1, "[INFO] Result saved to: %s\n", result_filename);
    DEBUG_PRINT(1, "[INFO] Solving time: %.3f seconds\n", solving_time);
    
    return satisfiable;
}

int main(void)
{
    while (1)
    {
        int mode;
        printf("\n1. CNF文件求解\n");
        printf("2. 游戏模式\n");
        printf("0. 退出程序\n");
        printf("请选择: ");
        
        if (scanf("%d", &mode) != 1)
        {
            while (getchar() != '\n');
            continue;
        }
        while (getchar() != '\n');

        if (mode == 0)
        {
            printf("已退出\n");
            break;
        }
        else if (mode == 1)
            cnf_mode();
        else if (mode == 2)
            sudoku_mode();
        else
            printf("请重新选择\n");
    }
    return 0;
}
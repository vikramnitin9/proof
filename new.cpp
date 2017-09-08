#include <iostream>
#include <vector>
#include <stack>
#include <string>
#include <cstdlib>
#include <sstream>
#include <assert.h>

using namespace std;

#define INF 2147483647

//Class for a variable. Has a unique id.
class var{
public:
	char id;
	var(char id){
		this->id = id;
	}
};

//Function to compare ids of two variables
bool cmp(var* a, var* b){
	return (a->id == b->id);
}

int nesting = 1;

class Pred{
public:
	//If predicate is a quantifier (ALL, EXISTS)
	//this stores which variable the quantifier applies to
	var* a;

	//In case of 'container' predicates like AND, NOT, etc.
	Pred* p;
	Pred* q;

	string name;
	vector< var* > v;

	int verified;

	bool is_verified(){return verified <= nesting;}

	Pred(string name){
		this->name = name;
		this->verified = INF;
	}

	Pred(){
		this->name = "Pred";
		this->verified = INF;
	}
};

string toString(Pred*);

//Function to check if two predicates are syntactically same
bool cmp(Pred* a, Pred* b){
	return (toString(a) == toString(b));
}

//Predicate which takes no arguments
class nullary_Pred: public Pred{
	nullary_Pred(){
	}
};

//Predicate which takes one variable as argument
class unary_Pred: public Pred{
public:
	unary_Pred(var* a){
		this->v.push_back(a);
	}
};

//Predicate which takes two variables as arguments
class binary_Pred: public Pred{
public:
	binary_Pred(var* a, var* b){
		this->v.push_back(a);
		this->v.push_back(b);
	}
};

//Predicate which takes three variables as arguments
class ternary_Pred: public Pred{
public:
	ternary_Pred(var* a, var* b, var* c){
		this->v.push_back(a);
		this->v.push_back(b);
		this->v.push_back(c);
	}
};

//Container for two predicates
class OR: public Pred {
public:
	OR(Pred* p, Pred* q){
		this->p = p;
		this->q = q;

		this->v.reserve( p->v.size() + q->v.size() );
		this->v.insert(v.end(), p->v.begin(), p->v.end());
		this->v.insert(v.end(), q->v.begin(), q->v.end());

		this->name = "OR";
	}
};

//Container for two predicates
class AND: public Pred {
public:
	AND(Pred* p, Pred* q){
		this->p = p;
		this->q = q;

		this->v.reserve( p->v.size() + q->v.size() );
		this->v.insert(v.end(), p->v.begin(), p->v.end());
		this->v.insert(v.end(), q->v.begin(), q->v.end());

		this->name = "AND";
	}
};

//Container for two predicates
class IMP: public Pred{
public:
	IMP(Pred* p, Pred* q){
		this->p = p;
		this->q = q;

		this->v.reserve( p->v.size() + q->v.size() );
		this->v.insert(v.end(), p->v.begin(), p->v.end());
		this->v.insert(v.end(), q->v.begin(), q->v.end());

		this->name = "IMP";
	}
};

//Container for one predicate
class NOT: public Pred{
public:
	NOT(Pred* p){
		this->p = p;
		this->v = p->v;
		this->verified = p->verified;

		this->name = "NOT";
	}
};

//Container for one predicate
class ALL: public Pred{
public:
	ALL(var* a, Pred* p){
		this->p = p;
		this->v = p->v;

		for(int i=0; i<v.size(); ++i){
			if(v[i] == a) this->a = v[i];
		}

		this->name = "ALL";
	}
};

//Container for one predicate
class EXISTS: public Pred{
public:
	EXISTS(var* a, Pred* p){
		this->p = p;
		this->v = p->v;

		for(int i=0; i<v.size(); ++i){
			if(cmp(v[i], a)) this->a = v[i];
		}

		this->name = "EXISTS";
	}
};

//Predicate to indicate contradiction
class CONTRA: public Pred{
public:
	CONTRA(){
		this->verified = nesting;
		this->name = "CONTRA";
	}
};

//Predicate to indicate a tautology
class TAUT: public Pred{
public:
	TAUT(){
		this->verified = nesting;
		this->name = "TAUT";
	}
};

//Rules for Natural Deduction in predicate logic
// p,q |- p^q
Pred* and_intro(Pred* p, Pred* q){
	if(p->is_verified() && q->is_verified()){
		AND* ret = new AND(p,q);
		ret->verified = nesting;
		return ret;
	}
	return NULL;
}

// p^q |- p
Pred* and_elim_1(Pred* c) {
	assert(c->name == "AND");
	return c->p;
}

// p^q |- q
Pred* and_elim_2(OR* c){
	assert(c->name == "OR");
	return c->q;
}

// p |- p|q
Pred* or_intro1(Pred* p, Pred* q){
	if(p->is_verified()){
		OR* ret = new OR(p,q);
		ret->verified = nesting;
		return ret;
	}
	return NULL;
}

// q |- p|q
Pred* or_intro2(Pred* p, Pred* q){
	if(q->is_verified()){
		OR* ret = new OR(p,q);
		ret->verified = nesting;
		return ret;
	}
	return NULL;
}

Pred* or_elim(Pred* c, Pred* r1, Pred* r2){
	assert(c->name == "OR" && r1->name == "IMP" && r2->name=="IMP");
	if(c->is_verified() && cmp(r1->p, c->p)
			&& cmp(r2->p, c->q) && cmp(r1->q, r2->q)){
		Pred* ret = r1->q;
		r1->q->verified = nesting;
		return ret;
	}
}

// !!p |- p
Pred* double_neg(Pred* c){
	assert(c->name == "NOT" && c->p->name == "NOT");
	c->p->p->verified = c->verified;
	return c->p->p;
}

// p, p->q |- q
Pred* imp_elim(Pred* c){
	assert(c->name == "IMP");
	if(c->p->is_verified()){
		c->q->verified = nesting;
		return c->q;
	}
}

Pred* imp_intro(Pred* p, Pred* q){
	if(q->verified == p->verified){
		IMP* ret = new IMP(p, q);
		ret->verified = p->verified;
		-- nesting;
		return ret;
	}
}

Pred* neg_intro(Pred* p, Pred* c){
	assert(c->name == "CONTRA");
	if(c->verified == p->verified){
		-- nesting;
		Pred* ret = new NOT(p);
		ret->verified = nesting;
		return ret;
	}
}

// _|_ |- p
Pred* contra_elim(Pred* c, Pred* p){
	assert(c->name == "CONTRA");
	if(c->is_verified()){
		p->verified = nesting;
		return p;
	}
	return NULL;
}

// p, !p |- _|_
Pred* contra_intro(Pred* p, Pred* c){
	assert(c->name == "NOT");
	if(p->is_verified() && cmp(c->p, p) && c->is_verified()){
		CONTRA* ret = new CONTRA();
		ret->verified = nesting;
		return ret;
	}
	return NULL;
}

// for all x p(x) |- p(x0)
Pred* all_sub(Pred* c, var* a){
	assert(c->name == "ALL");
	if(c->is_verified()){
		Pred* ret = c->p;
		for(int i=0; i<ret->v.size(); ++i){
			if(cmp(ret->v[i], c->a)) ret->v[i] = a;
		}
		return ret;
	}
	return NULL;
}

//Definitions of common predicates
class isZero: public unary_Pred{
public:
	isZero(var* a): unary_Pred(a){this->name = "isZero";}
};

class nat: public unary_Pred{
public:
	nat(var* a): unary_Pred(a){this->name = "nat";}
};

class eq: public binary_Pred{
public:
	eq(var* a, var* b): binary_Pred(a, b){this->name = "eq";}
};

class succ: public binary_Pred{
public:
	succ(var* a, var* b): binary_Pred(a, b){this->name = "succ";}
};

class sum: public ternary_Pred{
public:
	sum(var* a, var* b, var* c): ternary_Pred(a, b, c){this->name = "sum";}
};

void append_rec(Pred* c, string &s){
	ostringstream os;
	if(c->name == "ALL"){
		os << "For All " << c->a->id << " (";
		s.append(os.str());
		append_rec(c->p, s);
		cout << ")";
		return;
	}
	if(c->name == "EXISTS"){
		os << "There Exists" << c->a->id << " (";
		s.append(os.str());
		append_rec(c->p, s);
		cout << ")";
		return;
	}
	if(c->name == "IMP"){
		s.append("(");
		append_rec(c->p, s);
		s.append(" -> ");
		append_rec(c->q, s);
		s.append(")");
		return;
	}
	if(c->name == "AND"){
		s.append("(");
		append_rec(c->p, s);
		s.append(" AND ");
		append_rec(c->q, s);
		s.append(")");
		return;
	}
	if(c->name == "OR"){
		s.append("(");
		append_rec(c->p, s);
		s.append(" OR ");
		append_rec(c->q, s);
		s.append(")");
		return;
	}
	if(c->name == "NOT"){
		s.append("NOT (");
		append_rec(c->p, s);
		s.append(")");
		return;
	}
	os << c->name << "(";
	if(c->v.size() != 0) os << c->v[0]->id;

	for(int i=1; i<c->v.size(); ++i)
		os << ", " << c->v[i]->id ;

	os << ")";

	s.append(os.str());
}

string toString(Pred* c){
	string s = "";
	append_rec(c, s);
	return s;
}

//Base class for Axioms and Theorems
class Rule{
public:
	vector<Pred*> premises;
	Pred* result;

	Pred* premise(Pred* r){
		r->verified = nesting;
		this->premises.push_back(r);
		return r;
	}
};

//Does not require verification
class Axiom: public Rule{
public:
	void set_result(Pred* r){
		this->result = r;
	}
};

//Requires verification
class Theorem: public Rule{
	vector<Pred*> steps;

public:
	Pred* next_step(Pred* r){
		if(r == NULL) {
			cout << "Predicate is NULL\n";
		}
		if(!r->is_verified()){
			cout << "Step of theorem incorrect\n";
			cout << toString(r) << endl;
			exit(0);
		}
		steps.push_back(r);
		return r;
	}

	Pred* assume(Pred* r){
		steps.push_back(r);
		++ nesting;
		r -> verified = nesting;
		return r;
	}

	Pred* set_result(Pred* r){
		if(r->verified != 1){
			cout << "Could not set result!\n";
			exit(0);
		}
		this->result = r;
		return r;
	}
};


int main(){
	//Common variable names
	var a('a'), b('b'), c('c'), d('d'), e('e'), f('f');
	var x('x'), y('y'), z('z');

	#define a &a
	#define b &b
	#define c &c
	#define d &d
	#define e &e
	#define f &f
	#define x &x
	#define y &y
	#define z &z

	//The 9 Peano Axioms

	Axiom zero_nat;
	zero_nat.premise(new isZero(z));
	zero_nat.set_result(new nat(z));

	Axiom eq_ref;
	eq_ref.set_result(new eq(a, a));

	Axiom eq_symm;
	eq_symm.premise(new eq(a, b));
	eq_symm.set_result(new eq(b, a));

	Axiom eq_trans;
	eq_trans.premise(new eq(a, b));
	eq_trans.premise(new eq(b, c));
	eq_trans.set_result(new eq(a, c));

	Axiom nat_closure;
	nat_closure.premise(new nat(a));
	nat_closure.premise(new eq(a, b));
	nat_closure.set_result(new nat(b));

	Axiom succ_nat;
	succ_nat.premise(new nat(a));
	succ_nat.premise(new succ(a, b));
	succ_nat.set_result(new nat(b));

	Axiom succ_inj1;
	succ_inj1.premise(new eq(a, b));
	succ_inj1.premise(new succ(a, c));
	succ_inj1.premise(new succ(b, d));
	succ_inj1.set_result(new eq(c, d));
	Axiom succ_inj2;
	succ_inj2.premise(new eq(c, d));
	succ_inj2.premise(new succ(a, c));
	succ_inj2.premise(new succ(b, d));
	succ_inj2.set_result(new eq(a, b));

	Axiom zero_not_succ;
	zero_not_succ.premise(new isZero(z));
	zero_not_succ.premise(new nat(a));
	zero_not_succ.set_result(new NOT(new succ(a, z)));

	Axiom induction;
	Pred* p = new unary_Pred(a);
	Pred* q = new unary_Pred(b);

	induction.premise(new isZero(z));
	induction.premise(new unary_Pred(z));
	induction.premise(new ALL(a, new ALL(b,
							new IMP(new succ(a, b), new IMP(p, q)))));
	induction.set_result(new ALL(a, p));

	//---------------------------------------

	Axiom zero_sum;
	zero_sum.premise(new isZero(z));
	zero_sum.premise(new nat(a));
	zero_sum.set_result(new sum(a, z, a));

	Axiom def_sum; // a + succ(b) = succ(a+b)
	def_sum.premise(new sum(a, b, c));
	def_sum.premise(new succ(b, d));
	def_sum.premise(new succ(c, e));
	def_sum.set_result(new sum(a, d, e));

	//----------------------------------------

	Theorem LEM;

	Pred* r = new Pred();	Pred* pNot = new NOT(r);

		Pred* p1 = LEM.assume(new NOT(new OR(r, pNot)));

			Pred* p2 = LEM.assume(pNot);
			Pred* p3 = LEM.next_step(or_intro2(r, pNot));
			Pred* p4 = LEM.next_step(contra_intro(p3, p1)); //needs to be fixed

		Pred* p5 = LEM.next_step(neg_intro(p2, p4));
		Pred* p6 = LEM.next_step(double_neg(p5));
		Pred* p7 = LEM.next_step(or_intro1(p6, pNot));
		Pred* p8 = LEM.next_step(contra_intro(p7, p1)); //needs to be fixed

	Pred* p9 = LEM.next_step(neg_intro(p1, p8));
	Pred* p10 = LEM.next_step(double_neg(p9));
	LEM.set_result(p10);

	cout << toString(p10) << endl;

	return 0;
}

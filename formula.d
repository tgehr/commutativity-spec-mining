module formula;
__gshared: // (necessary for hacky timeout implementation)

import std.stdio, std.conv, std.algorithm, std.range, std.array;

import std.typecons, std.ascii;
import hashtable,util;

struct UnorderedPair(T){
	Seq!(T,T) elements;
	alias elements this;
	bool opEquals(UnorderedPair rhs){ return elements == rhs.elements || elements[1]==rhs.elements[0]&&elements[0]==rhs.elements[1]; }
	size_t toHash(){ return typeid(typeof(elements[0])).getHash(&elements[0]) + typeid(typeof(elements[0])).getHash(&elements[1]); }
}
auto unorderedPair(T)(T e1, T e2){ return UnorderedPair!T(e1,e2); }
alias UP=UnorderedPair;
alias up=unorderedPair;

struct TupleX(T...){
	T expand;
	alias expand this;
	hash_t toHash(){
		auto r=fnvb;
		foreach(ref x;expand) r=FNV(x.toHash(),r);
		return r;
	}
}
auto tuplex(T...)(T t){ return TupleX!T(t); }

enum Precedence{
	none,
	quantifier,
	equivalence,
	implication,
	xor,
	or,
	and,
	not,
	atom,
}

abstract class Formula{
	override string toString(){
		return toStringImpl(Precedence.none);
	}
	abstract string toStringImpl(Precedence prec);
	abstract @property Precedence precedence();
	protected final string addp(Precedence prec, string s){
		return prec > precedence? "(" ~ s ~ ")":s;
	}
}

class True: Formula{
	private this(){}
	override string toStringImpl(Precedence prec){ return "true"; }
	override @property Precedence precedence(){ return precedence.none; }
}
True tt;
class False: Formula{
	private this(){}
	override string toStringImpl(Precedence prec){ return "false"; }
	override @property Precedence precedence(){ return precedence.none; }
}
False ff;
static this(){ tt=new True; ff=new False; }

abstract class Operator: Formula{
	abstract @property string symbol();
}

alias SetX(T)=HSet!(T,(a,b)=>a==b,a=>a.toHash());
alias FormulaSet=SetX!Formula;

auto inOrder(S)(S s){
	S.T[] r;
	foreach(x;s) r~=x;
	import std.algorithm;
	string toStr(Formula f){
		import std.string;
		auto s=f.toString();
		s=s.filter!(c=>!"¬| ".canFind(c)).to!string;
		s=s.replace("≠","=");
		s.replace("<","=");
		return s;
	}
	r.schwartzSort!toStr();
	return r;
}

abstract class CommutAssocIdemOp: Operator{
	FormulaSet operands;
	protected mixin template Constructor(){ this(FormulaSet e)in{assert(e.length>1); }body{ operands=e; } }
	override string toStringImpl(Precedence prec){
		string r;
		if(operands.length>20) foreach(o;operands) r~=symbol~" "~o.toStringImpl(precedence);
		else foreach(o;operands.inOrder) r~=symbol~" "~o.toStringImpl(precedence);
		return addp(prec, r[symbol.length+1..$]);
	}
}

abstract class BinaryOp: Operator{
	Formula[2] operands;
	protected mixin template Constructor(){ this(Formula e1, Formula e2){ operands=[e1,e2]; } }
	override string toStringImpl(Precedence prec){
		return addp(prec, operands[0].toStringImpl(precedence) ~ " " ~ symbol ~ " " ~ operands[1].toStringImpl(precedence));
	}
	abstract BinaryOp construct(Formula a, Formula b);
}
abstract class UnaryOp: Operator{
	Formula operand;
	override string toStringImpl(Precedence prec){
		return addp(prec, symbol~" "~operand.toStringImpl(precedence));
	}
}

void resetUniqueMaps(){
	uniqueMapCommutative=typeof(uniqueMapCommutative).init;
	uniqueMapCommutAssocIdem=typeof(uniqueMapCommutAssocIdem).init;
	uniqueMapNonCommutAssocIdem=typeof(uniqueMapNonCommutAssocIdem).init;
	uniqueMapUnary=typeof(uniqueMapUnary).init;
}

MapX!(TupleX!(typeof(typeid(Formula)),UPF),Formula) uniqueMapCommutative;
auto uniqueFormulaCommutative(T)(Formula e1, Formula e2){
	if(auto t1=cast(Terminal)e1)
		if(auto t2=cast(Terminal)e2)
			if(t1.name>t2.name)
				swap(e1,e2);
	auto t=tuplex(typeid(T),up(e1,e2));
	if(t in uniqueMapCommutative) return cast(T)uniqueMapCommutative[t];
	auto r=new T(e1,e2);
	uniqueMapCommutative[t]=r;
	return r;
}

alias MapX(K,V) = HashMap!(K,V,(a,b)=>a==b,a=>a.toHash());
MapX!(TupleX!(typeof(typeid(Formula)),FormulaSet),Formula) uniqueMapCommutAssocIdem;
MapX!(TupleX!(typeof(typeid(Formula)),Formula,Formula),Formula) uniqueMapNonCommutAssocIdem;
auto uniqueFormulaCommutAssocIdem(T)(FormulaSet e){
	auto t=tuplex(typeid(T),e);
	if(t in uniqueMapCommutAssocIdem) return cast(T)uniqueMapCommutAssocIdem[t];
	auto r=new T(e);
	uniqueMapCommutAssocIdem[t]=r;
	return r;
}
auto uniqueFormulaNonCommutAssocIdem(T)(Formula a, Formula b){
	auto t=tuplex(typeid(T),a,b);
	if(t in uniqueMapNonCommutAssocIdem) return cast(T)uniqueMapNonCommutAssocIdem[t];
	auto r=new T(a,b);
	uniqueMapNonCommutAssocIdem[t]=r;
	return r;
}
MapX!(TupleX!(typeof(typeid(Formula)),Formula),Formula) uniqueMapUnary;
auto uniqueFormulaUnary(T)(Formula a){
	auto t=tuplex(typeid(T),a);
	if(t in uniqueMapUnary) return cast(T)uniqueMapUnary[t];
	auto r=new T(a);
	uniqueMapUnary[t]=r;
	return r;
}
string lowerf(string s){ return s.length?toLower(s[0])~s[1..$]:s; }
string makeConstructorCommutative(T)(){
	return "auto " ~ lowerf(__traits(identifier, T))~"(Formula e1, Formula e2){ return uniqueFormulaCommutative!("~__traits(identifier,T)~")(e1,e2); }";
}
string makeConstructorCommutAssocIdem(T,string dflt=null)(){
	return "auto " ~ lowerf(__traits(identifier, T))~"(FormulaSet f){ auto fsh=f.shallow!"~__traits(identifier,T)~"; if(fsh.length==1) foreach(x;fsh) return x; "~(dflt.length?"if(!fsh.length) return "~dflt~";":"")~"return uniqueFormulaCommutAssocIdem!("~__traits(identifier,T)~")(fsh); }" ~
		"auto " ~ lowerf(__traits(identifier, T))~"(Formula e1,Formula e2){ FormulaSet a;a.insert(e1);a.insert(e2);return "~lowerf(__traits(identifier, T))~"(a); }";

}
string makeConstructorNonCommutAssocIdem(T)(){
	return "auto " ~ lowerf(__traits(identifier, T))~"(Formula e1, Formula e2){ return uniqueFormulaNonCommutAssocIdem!("~__traits(identifier,T)~")(e1,e2); }";
}

FormulaSet shallow(T)(FormulaSet arg){
	FormulaSet r;
	foreach(x;arg){
		if(auto t=cast(T)x){
			foreach(y;t.operands)
				r.insert(y);
		}
	}
	if(!r.length) return arg;
	foreach(x;arg)
		if(!cast(T)x) r.insert(x);
	return r;
}

alias UPF=UP!Formula;
class And: CommutAssocIdemOp{
	mixin Constructor;
	override @property string symbol(){ return "∧"; }
	override @property Precedence precedence(){ return Precedence.and; }
}
mixin(makeConstructorCommutAssocIdem!(And,"tt"));
//auto and(Formula e1, Formula e2){ return uniqueFormula!And(e1,e2); }

class Or: CommutAssocIdemOp{
	mixin Constructor;
	override @property Precedence precedence(){ return Precedence.or; }
	override string symbol(){ return "∨"; }
}
mixin(makeConstructorCommutAssocIdem!(Or,"ff"));

class Not: UnaryOp{
	this(Formula operand){ this.operand=operand; }
	override @property string symbol(){ return "¬"; }
	override string toStringImpl(Precedence prec){
		if(auto e=cast(Eq)operand)
			return addp(prec, e.operands[0].toStringImpl(e.precedence) ~ " ≠ " ~ e.operands[1].toStringImpl(e.precedence));
		if(auto l=cast(Lt)operand){
			return addp(prec, l.operands[1].toStringImpl(l.precedence) ~ " ≤ " ~ l.operands[0].toStringImpl(l.precedence));
		}
		return super.toStringImpl(prec);
	}
	override @property Precedence precedence(){
		if(auto e=cast(Eq)operand)
			return e.precedence;
		return Precedence.not;
	}
}
auto not(Formula op){
	if(auto n=cast(Not)op) return n.operand;
	return uniqueFormulaUnary!Not(op);
}
class Terminal: Formula{
	string name;
	this(string name){ this.name = name; }
	override string toStringImpl(Precedence prec){ return name; }
	override @property Precedence precedence(){ return Precedence.none; }
}
Terminal t(string n){ return new Terminal(n); }

abstract class AtomicOp: BinaryOp{
	override @property Precedence precedence(){ return Precedence.atom; }
}

class Eq: AtomicOp{
	this(Formula a, Formula b){ operands[0]=a; operands[1]=b; }
	override @property string symbol(){ return "="; }
	override Eq construct(Formula a, Formula b){
		return eq(a,b);
	}
}
mixin(makeConstructorCommutative!Eq);

class Lt: AtomicOp{
	this(Formula a, Formula b){ operands[0]=a; operands[1]=b; }
	override @property string symbol(){ return "<"; }
	override Lt construct(Formula a, Formula b){
		return lt(a,b);
	}
}
mixin(makeConstructorNonCommutAssocIdem!Lt);

class Exists: Formula{
	Terminal t;
	Formula f;

	this(Terminal t,Formula f){ this.t=t; this.f=f; }
	override @property Precedence precedence(){ return Precedence.quantifier; }
	override string toStringImpl(Precedence prec){
		return addp(prec,"∃ "~t.toString()~": "~f.toStringImpl(precedence));
	}
}

class ForAll: Formula{
	Terminal t;
	Formula f;

	this(Terminal t,Formula f){ this.t=t; this.f=f; }
	override @property Precedence precedence(){ return Precedence.quantifier; }
	override string toStringImpl(Precedence prec){
		return addp(prec,"∀ "~t.toString()~": "~f.toStringImpl(precedence));
	}
}

void visit(T)(ref T result,Formula f){
	alias Seq!(__traits(getOverloads,T,"perform")) overloads;
	if(auto a=cast(And)f) foreach(o;a.operands) visit(result,o);
	if(auto a=cast(Or)f) foreach(o;a.operands) visit(result,o);
	if(auto a=cast(Eq)f) foreach(o;a.operands) visit(result,o);
	if(auto a=cast(Lt)f) foreach(o;a.operands) visit(result,o);
	if(auto a=cast(Not)f) visit(result,a.operand);
	foreach(i, ov; overloads){
		import std.traits;
		if(auto e = cast(ParameterTypeTuple!(ov)[0])f){
			result.perform(e);
			return;
		}
	}
}

Formula rewrite(alias g)(Formula f){
	import util;
	alias rec=rewrite!g;
	if(auto a=cast(And)f){
		FormulaSet s;
		foreach(o;a.operands) s.insert(rec(o));
		return g(and(s));
	}else if(auto a=cast(Or)f){
		FormulaSet s;
		foreach(o;a.operands) s.insert(rec(o));
		return g(or(s));
	}else if(auto a=cast(Eq)f){
		Formula[2] ops=a.operands;
		foreach(ref o;ops) o=rec(o);
		return g(eq(ops[0],ops[1]));
	}else if(auto a=cast(Lt)f){
		Formula[2] ops=a.operands;
		foreach(ref o;ops) o=rec(o);
		return g(lt(ops[0],ops[1]));
	}else if(auto a=cast(Not)f){
		return g(not(rec(a.operand)));
	}
	return g(f);
}

struct UnionRep(T, alias smaller){
	T[T] rep;
	T[T] smallest;
	private void add(T a){
		if(a!in rep){
			rep[a]=a;
			smallest[a]=a;
		}
	}
	T find(T arg){
		if(rep[arg] is arg) return arg;
		return rep[arg]=find(rep[arg]);
	}
	void unite(T a,T b){
		if(!a||!b) return;
		add(a), add(b);
		auto fa=find(a),fb=find(b);
		if(smaller(smallest[fb],smallest[fa])) smallest[fa]=smallest[fb];
		rep[fb]=rep[fa];
	}
	T[T] get(){
		foreach(k,ref v;rep){ while(v!=rep[v]) v=rep[v]; }
		foreach(k,ref v;rep) v=smallest[v];
		return rep;
	}
}

void mapThrough(T,S...)(T[T] x, ref S args){ foreach(ref a;args) if(a in x) a=x[a]; }

Terminal[Terminal] buildNormalizationTable(Formula f){
	UnionRep!(Terminal,(a,b)=>a.name<b.name) rep;
	foreach(o;f.conjuncts) if(auto e=cast(Eq)o) rep.unite(cast(Terminal)e.operands[0],cast(Terminal)e.operands[1]);
	return rep.get();
}

Formula applyNormalizationTable(Formula f, Terminal[Terminal] rr, bool normalizeEq){
	Formula doit(Formula o){
		if(auto l=cast(Lt)o){
			auto op0=cast(Terminal)l.operands[0], op1=cast(Terminal)l.operands[1];
			mapThrough(rr,op0,op1);
			return lt(op0,op1);
		}
		if(auto n=cast(Not)o){
			if(auto e=cast(Eq)n.operand){
				auto op0=cast(Terminal)e.operands[0], op1=cast(Terminal)e.operands[1];
				mapThrough(rr,op0,op1);
				return not(eq(op0,op1));
			}
		}
		if(normalizeEq){
			if(auto e=cast(Eq)o){
				auto op0=cast(Terminal)e.operands[0], op1=cast(Terminal)e.operands[1];
				if(op0 !is op1){
					auto nop0=op0, nop1=op1;
					mapThrough(rr,nop0,nop1);
					if(nop0 !is nop1) return eq(nop0,nop1);
					auto e0=nop0 !is op0?eq(nop0,op0):null;
					auto e1=nop1 !is op1?eq(nop1,op1):null;
					if(!e0){ assert(e1); return e1; }
					if(!e1) return e0;
					return e0.and(e1);
				}
			}
		}
		return o;
	}
	return f.rewrite!doit();
}

Formula normalize(Formula f){
	if(auto a=cast(And)f){
		auto rr=buildNormalizationTable(a);
		auto r=a.applyNormalizationTable(rr,true);
		FormulaSet fs;
		auto conj=r.conjuncts;
		foreach(x;conj){
			auto xn=x.normalize;
			if(xn is ff) return ff;
			if(not(xn) in conj) return ff;
			if(auto l=cast(Lt)xn){
				if(lt(l.operands[1],l.operands[0]) in conj)
					return ff;
				if(eq(l.operands[0],l.operands[1]) in conj)
					return ff;
			}
			if(auto n=cast(Not)xn){
				if(auto e=cast(Eq)n.operand){
					if(lt(e.operands[0],e.operands[1]) in conj)
						continue;
					if(lt(e.operands[1],e.operands[0]) in conj)
						continue;
				}
			}
			if(xn !is tt) fs.insert(xn);
		}
		return and(fs).unclose;
	}
	if(auto a=cast(Or)f){
		FormulaSet fs;
		foreach(x;a.operands){
			if(x is tt) return tt;
			if(x !is ff) fs.insert(x.normalize);
		}
		return or(fs);
	}
	if(auto n=cast(Not)f){
		if(n.operand is tt) return ff;
		if(n.operand is ff) return tt;
		return n;
	}
	if(auto e=cast(Eq)f){
		if(e.operands[0] is e.operands[1]) return tt;
		return e;
	}
	if(auto l=cast(Lt)f){
		if(l.operands[0] is l.operands[1]) return ff;
		return l;
	}
	return f;
}

Formula negationNormalForm(Formula f){
	if(auto n=cast(Not)f){
		if(auto a=cast(And)n.operand){
			FormulaSet r;
			foreach(op;a.operands)
				r.insert(negationNormalForm(not(op)));
			return or(r);
		}else if(auto a=cast(Or)n.operand){
			FormulaSet r;
			foreach(op;a.operands)
				r.insert(negationNormalForm(not(op)));
			return and(r);
		}
	}
	return f;
}

Formula close(bool unclose=false)(Formula f){
	auto a=cast(And)f;
	if(!a) return f;
	FormulaSet s=a.operands;
	bool dupped=false;
	bool deduce(Formula lxy){
		if((!unclose)^(lxy in s)){
			if(!dupped){ s=s.dup(); dupped=true; }
			static if(!unclose) s.insert(lxy);
			else s.remove(lxy);
			return true;
		}
		return false;
	}
 Lfor:for(;;){
		foreach(x;s) foreach(y;s)
			if(auto lx=cast(Lt)x)
				if(auto ly=cast(Lt)y)
					if(lx.operands[1] is ly.operands[0])
						if(deduce(lt(lx.operands[0],ly.operands[1])))
							continue Lfor;
		break;
	}
	return and(s);
}
alias unclose=close!true;

FormulaSet conjuncts(Formula f){
	if(auto a=cast(And)f) return a.operands;
	FormulaSet s;
	s.insert(f);
	return s;
}
FormulaSet disjuncts(Formula f){
	if(auto a=cast(Or)f) return a.operands;
	FormulaSet s;
	s.insert(f);
	return s;
}

auto unite(S,T)(S a,T b){
	import std.traits;
	SetX!(CommonType!(S.T,T.T)) r;
	foreach(x;a) r.insert(x);
	foreach(y;b) r.insert(y);
	return r;
}

auto setMinus(S,T)(S a,T b){
	import std.traits;
	SetX!(CommonType!(S.T,T.T)) r;
	foreach(x;a) if(x !in b) r.insert(x);
	return r;
}


bool subset(S)(S a,S b){
	foreach(x;a) if(x !in b) return false;
	return true;
}

Formula factorGreedily(Formula f){
	auto o=cast(Or)f;
	if(!o) return f; // TODO: distributivity also holds the other way!
	for(;;){
		auto max=tuple(cast(size_t)0,cast(size_t)0);
		FormulaSet cnj;
		size_t countOccurrences(FormulaSet s){
			size_t r=0;
			foreach(dsj;f.disjuncts)
				if(s.subset(dsj.conjuncts))
					r++;
			return r;
		}
		foreach(dsj;f.disjuncts){
			foreach(subs;dsj.conjuncts.subsets){
				if(!subs.length) continue;
				auto c=countOccurrences(subs);
				auto t=tuple(c,subs.length);
				if(t>max){
					max=t;
					cnj=subs;
				}
			}
		}
		if(max[0]<=1) return f;
		FormulaSet newDisjuncts;
		FormulaSet oldDisjuncts;
		foreach(dsj;f.disjuncts)
			if(cnj.subset(dsj.conjuncts))
				newDisjuncts.insert(and(dsj.conjuncts.setMinus(cnj)));
			else
				oldDisjuncts.insert(dsj);
		f=and(or(newDisjuncts),and(cnj)).or(or(oldDisjuncts)).normalize;
	}
}

import util;
Formula getFormula(ref OrderedPartition op, Terminal[] ints){
	Formula r=tt;
	void add(Formula φ){
		r=r is tt?φ:r.and(φ);
	}
	foreach(i,x;op.p){
		foreach(y;1..x.length)
			add(eq(ints[x[y-1]],ints[x[y]]));
		if(i+1<op.p.length)
			add(lt(ints[x[$-1]],ints[op.p[i+1][0]]));
	}
	return r;
}

bool evaluate(Formula a, bool[Terminal] bools,Terminal[] ints,OrderedPartition order){ // TODO: get rid of this and use the evaluate from below instead?
	size_t[Terminal] index;
	foreach(i;0..order.p.length)
		foreach(t;order.p[i])
			index[ints[t]]=i;
	size_t evali()(Formula a){
		if(auto t=cast(Terminal)a) return index[t];
		assert(0);
	}
	bool evalb()(Formula a){
		if(a is tt) return true;
		if(a is ff) return false;
		if(auto n=cast(Not)a) return !evalb(n.operand);
		if(auto e=cast(Eq)a)
			return evali(cast(Terminal)e.operands[0])
				== evali(cast(Terminal)e.operands[1]);
		if(auto l=cast(Lt)a)
			return evali(cast(Terminal)l.operands[0])
				< evali(cast(Terminal)l.operands[1]);
		if(auto aa=cast(And)a){
			foreach(x;aa.operands) if(!evalb(x)) return false;
			return true;
		}
		if(auto aa=cast(Or)a){
			foreach(x;aa.operands) if(evalb(x)) return true;
			return false;
		}
		if(auto t=cast(Terminal)a) return bools[t];
		assert(0);
	}
	return evalb(a);
}

enum Type{
	none_,
	bool_,
	int_,
	tuple_,
}
struct Value{
	this(int r){ this.r=r; tt=Type.int_; }
	this(bool r){ this.r=r; tt=Type.bool_; }
	this(T...)(Tuple!T args){
		a=[];
		foreach(x;args) a~=Value(x);
		tt=Type.tuple_;
	}
	@property Type type(){ return tt; }
	int int_()in{assert(type==Type.int_);}body{ return r; }
	bool bool_()in{assert(type==Type.bool_);}body{ return !!r; }
	Value[] tuple_()in{assert(type==Type.tuple_);}body{ return a; }

	T get(T)(){ static if(is(T==int)) return int_; static if(is(T==bool)) return bool_; }

	string toString(){ return tt==Type.bool_?(!!r).to!string:tt==Type.int_?r.to!string:"()"; }
	int opCmp(Value b)in{assert(type!=Type.tuple_);}body{ return type==b.type?(r==b.r?0:r<b.r?-1:1):type==Type.int_?-1:1; }
private:
	Type tt;
	int r;
	Value[] a; // TODO: it would be nice if this wouldn't slow down everything so much -> use r as pointer?
}

Value[] expandTuples(Value[] v){
	if(v.all!(a=>a.type!=Type.tuple_)) return v;
	Value[] r;
	foreach(x;v){
		if(x.type==Type.tuple_) r~=x.tuple_;
		else r~=x;
	}
	return r.expandTuples();
}

struct Assignment{
	this(Terminal[] variables, Value[] values)in{assert(variables.length==values.length);}body{
		this.variables=variables, this.values=values;
	}
	Value opIndex(Terminal variable){
		foreach(i,v;variables) if(v is variable) return values[i];
		assert(0,text("range error: have ",variables," looked for ",variable));
	}
	int opApply(scope int delegate(Terminal,ref Value) dg){
		foreach(i,v;variables) if(auto r=dg(v,values[i])) return r;
		return 0;
	}
	string toString(){
		string r="{";
		foreach(i,v;variables) r~=(i?",":"")~v.to!string~" → "~values[i].to!string;
		r~="}";
		return r;
	}
	Assignment swap(Terminal t1, Terminal t2){
		auto r=Assignment(variables,values.dup);
		auto v1=this[t1],v2=this[t2];
		foreach(ref x;r.values)
			if(x==v1) x=v2;
			else if(x==v2) x=v1;
		return r;
	}
	Assignment updateAll(Terminal t,Value v){ // for integer variables
		auto r=Assignment(variables,values.dup);
		auto vt=this[t];
		foreach(ref x;r.values) if(x==vt) x=v;
		return r;
	}
	Assignment update(Terminal t,Value v){
		auto r=Assignment(variables,values.dup);
		foreach(i,ref x;r.values) if(variables[i] is t) x=v;
		return r;
	}

	Assignment extend(Assignment b){
		return Assignment(variables~b.variables,values~b.values);
	}

	Assignment increase(Terminal t){
		// TODO: this is a hack, fix
		size_t p=-1;
		foreach(i,v;variables) if(v==t) p=i;
		auto values=this.values.dup;
		void inc(size_t p){
			foreach(i,x;values)
				if(x.type==Type.int_&&x.int_==values[p].int_+1)
					inc(i);
		}
		inc(p);
		return Assignment(variables,values);
	}

	bool areAdjacent(Terminal a, Terminal b){
		auto va=this[a], vb=this[b];
		if(va==vb) return false;
		if(vb<va) .swap(va,vb);
		foreach(t,val;this) if(va<val && val<vb) return false;
		return true;
	}

private:
	Terminal[] variables;
	Value[] values;
}
bool evaluate(Formula f, Assignment a){
	bool eval(Formula f){
		if(f is tt) return true;
		if(f is ff) return false;
		if(auto n=cast(Not)f) return !eval(n.operand);
		if(auto e=cast(Eq)f)
			return a[cast(Terminal)e.operands[0]]==a[cast(Terminal)e.operands[1]];
		if(auto l=cast(Lt)f)
			return a[cast(Terminal)l.operands[0]]<a[cast(Terminal)l.operands[1]];
		if(auto aa=cast(And)f){
			foreach(x;aa.operands) if(!eval(x)) return false;
			return true;
		}
		if(auto aa=cast(Or)f){
			foreach(x;aa.operands) if(eval(x)) return true;
			return false;
		}
		if(auto t=cast(Terminal)f) return a[t].bool_;
		assert(0);
	}
	return eval(f);
}

Tuple!(SetX!Terminal,SetX!Terminal) getVariables(Formula f){
	SetX!Terminal ints;
	SetX!Terminal bools;
	void doit(Formula g){
		if(auto n=cast(Not)g)
			return doit(n.operand);
		if(auto eq=cast(Eq)g){
			ints.insert(cast(Terminal)eq.operands[0]);
			ints.insert(cast(Terminal)eq.operands[1]);
			return;
		}
		if(auto lt=cast(Lt)g){
			ints.insert(cast(Terminal)lt.operands[0]);
			ints.insert(cast(Terminal)lt.operands[1]);
			return;
		}
		if(auto cmt=cast(CommutAssocIdemOp)g){
			foreach(o;cmt.operands) doit(o);
			return;
		}
		if(auto t=cast(Terminal)g) bools.insert(t);
	}
	doit(f);
	return tuple(ints,bools);
}

struct AllAssignments{
	Terminal[] ints,bools;
	int opApply(scope int delegate(bool[Terminal] vbools, OrderedPartition op) dg){
		int visitAll(OrderedPartition op, int x){
			if(x==ints.length){
				bool[Terminal] vbools;
				int visitAllBools(int y){
					if(y==bools.length)
						return dg(vbools,op);
					foreach(bb;0..2){
						vbools[bools[y]]=!!bb;
						if(auto r=visitAllBools(y+1))
							return r;
					}
					return 0;
				}
				return visitAllBools(0);
			}
			foreach(i;0..2*op.length+1){
				auto np=op.dup();
				np.addAt(x,i);
				if(auto r=visitAll(np,x+1)) return r;
			}
			return 0;
		}
		return visitAll(OrderedPartition(),0);
	}
}

bool equivalent(Formula a, Formula b){
	auto vbla=getVariables(a);
	auto vblb=getVariables(b);
	auto ints=vbla[0].unite(vblb[0]).array;
	auto bools=vbla[1].unite(vblb[1]).array;
	foreach(vbools,op;AllAssignments(ints,bools)){
		auto b=evaluate(a,vbools,ints,op)==evaluate(b,vbools,ints,op);
		// version(VERBOSE) if(!b) writeln("failed on ",vbools,ints,op);
		if(!b) return false;
	}
	return true;
}

bool checkImplies(Formula a, Formula b){
	auto vbla=getVariables(a);
	auto vblb=getVariables(b);
	auto ints=vbla[0].unite(vblb[0]).array;
	auto bools=vbla[1].unite(vblb[1]).array;
	foreach(vbools,op;AllAssignments(ints,bools)){
		if(evaluate(a,vbools,ints,op)&&!evaluate(b,vbools,ints,op)){
			return false;
		}
	}
	return true;
}

size_t equivClassHash(Formula f,Tuple!(Terminal[],Terminal[]) vbl){
	size_t h=fnvb;
	foreach(vbools,op;AllAssignments(vbl.expand)){
		auto b=evaluate(f,vbools,vbl[0],op);
		h=FNV(b,h);
	}
	return h;
}

size_t size(Formula f){
	if(!f) return 0;
	static struct S{
		int s=0;
		void perform(CommutAssocIdemOp o){ s+=o.operands.length-1; }
		void perform(Not n){ if(cast(CommutAssocIdemOp) n.operand) s++; }
		void perform(BinaryOp b){ s--; }
		void perform(Formula f){ s++; }
	}
	S s;
	s.visit(f);
	return s.s;
}

auto forEach(alias a,T...)(Tuple!T arg){
	alias F(T)=typeof(a(T.init));
	alias Seq(T...)=T;
	template staticMap(alias F,T...){
		static if(!T.length) alias staticMap=T;
		else alias staticMap=Seq!(F!(T[0]),staticMap!(F,T[1..$]));
	}
	Tuple!(staticMap!(F,T)) r;
	foreach(i,ref x;r) x=a(arg[i]);
	return r;
}


Formula[] allBasicPredicates(Tuple!(Terminal[],Terminal[]) variables,bool lt=true){
	auto ints=variables[0], bools=variables[1];
	auto preds=chain(bools,
					 cartesianProduct(ints,ints)
					 .map!(a=>(lt&&a[0]!is a[1]?[cast(Formula)a[0].lt(a[1])]:[])~(a[0].name<a[1].name?[cast(Formula)eq(a[0],a[1])]:[]))
					 .joiner);
	return preds.map!(a=>[a,not(a)]).joiner.array;
}

import std.array;
import std.datetime.stopwatch;
Formula[] allFormulasOfSize(T,alias filter=_=>true)(size_t s,ref Formula[][][2] memo,Duration timeout=0.hnsecs){
	bool to=timeout!=0.hnsecs;
	StopWatch sw; if(to) sw.start();
	enum index=is(T==And)?0:1;
	if(memo[index].length<=s) memo[index].length=(s*2)+1;
	if(memo[index][s].length||s==1) return memo[index][s];
	if(s==0){
		static if(is(T==And)) return filter(tt)?[tt]:[];
		else return filter(ff)?[ff]:[];
	}
	if(!(s&1)) return memo[index][s]; // all other valid sizes are actually odd numbers
	// if(s==1){ assert(0,"need to provide basic predicates"); }
	static if(is(T==And)){ alias cons=and; alias Other=Or; }
	else static if(is(T==Or)){ alias cons=or; alias Other=And; }
	else static assert(0);

	void create(size_t curSize,size_t totalSize,FormulaSet fs){
		if(to&&sw.peek()>timeout){ memo[index][s]=[]; return; }
		auto remainder=s-totalSize;
		assert(remainder>=0);
		if(!remainder){
			auto f=cons(fs);
			assert(f.size==s,text(cons(fs)," ",s," ",f.size));
			if(filter(f)) memo[index][s]~=f;
			return;
		}
		auto smaller=allFormulasOfSize!(Other,filter)(curSize,memo);
		auto n=smaller.length;
		for(size_t k=0,newTotalSize=totalSize;k<=n;k++,newTotalSize+=(newTotalSize!=0)+curSize){
			void insertPartition(int num,size_t cur,FormulaSet fs){
				if(num==k){ return create(curSize+2,newTotalSize,fs); }
				foreach(i;cur..n-(k-1-num)){
					// pruning possibility:
					if(not(smaller[i]) in fs) continue; // TODO: de-morgan?
					auto fsp=fs.dup();
					fsp.insert(smaller[i]);
					insertPartition(num+1,i+1,fsp);
				}
			}
			if(newTotalSize>s) break;
			bool reachable(size_t remainder,size_t minSize)in{ // TODO: compute bounds on k instead
				assert(!(remainder&1),text(remainder));
			}body{
				if(!remainder) return true;
				if(remainder==(minSize+1)) return true;
				if(remainder>=2*(minSize+1)) return true;
				return false;
			}
			if(reachable(s-(k?newTotalSize:1),curSize+2))
				insertPartition(0,0,fs);
		}
	}
	if(s>=3){
		FormulaSet fs;
		create(1,0,fs);
	}
	return memo[index][s];
}

auto allFormulasOfSize(alias filter=_=>true)(size_t s, ref Formula[][][2] memo,Duration timeout=0.hnsecs){
	auto to=timeout!=0.hnsecs;
	StopWatch sw; if(to) sw.start();
	auto a=allFormulasOfSize!(And,filter)(s,memo,timeout);
	auto b=s==1?[]:allFormulasOfSize!(Or,filter)(s,memo,to?timeout-sw.peek():timeout);
	return chain(a,b);
}

struct EquivFormula{
	Formula f;
	this(Formula f,Tuple!(Terminal[],Terminal[]) vbl){
		this.f=f;
		theHash=f.equivClassHash(vbl);
	}
	bool opEquals(EquivFormula rhs){ return theHash == rhs.theHash && equivalent(f,rhs.f); }
	size_t toHash(){ return theHash; }
private:
	size_t theHash;
}

struct NonEquivalentMinimalFormulas{
	this(Tuple!(Terminal[],Terminal[]) vbl,size_t sizeLimit, Formula[] bp){
		this.vbl=vbl; this.sizeLimit=sizeLimit;
		//if(!bp) bp=vbl.allBasicPredicates(true);
		foreach(index;0..2){
			memo[index].length=2;
			memo[index][1]=bp;
		}
	}
	int opApply(scope int delegate(EquivFormula) dg){
		foreach(s;0..sizeLimit){
			foreach(g;allFormulasOfSize!((f){
						auto feq=EquivFormula(f,vbl);
						if(feq in minSet) return false;
						minSet.insert(feq);
						hashesMap[f]=feq;
						return true;})(s,memo)){
				if(g !in hashesMap) hashesMap[g]=EquivFormula(g,vbl);
				if(auto r=dg(hashesMap[g])) return r;
			}
		}
		return 0;
	}
private:
	size_t sizeLimit;
	Tuple!(Terminal[],Terminal[]) vbl;
	Formula[][][2] memo;
	HSet!(EquivFormula,(a,b)=>a==b,a=>a.toHash()) minSet;
	HashMap!(Formula,EquivFormula,(a,b)=>a is b, a=>a.toHash()) hashesMap; // TODO: this is a hack.
}

bool hasLt(Formula f){
	static struct S{
		bool b=false;
		void perform(Lt lt){ b=true; }
	}
	S s;
	s.visit(f);
	return s.b;
}

Formula minimalEquivalent(Formula f,Formula[] bp){
	auto vbl=getVariables(f).forEach!(a=>a.array);
	Formula[][][2] memo;
	auto fhash=f.equivClassHash(vbl);
	foreach(EquivFormula g;NonEquivalentMinimalFormulas(vbl,f.size,bp)){
		version(VERY_VERBOSE) writeln("considering formula ",g.f," ",g.toHash());
		if(g.toHash()!=fhash) continue;
		if(g.f.equivalent(f))
			return g.f;
	}
	return f;
}

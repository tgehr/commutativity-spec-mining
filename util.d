alias ID(alias a)=a;
alias Seq(T...)=T;

import datatypes;
import std.range, std.algorithm, std.conv, std.array;

struct OrderedPartition{
	@property size_t length(){ return p.length; }
	void addAt(int x, size_t i)in{assert(i<2*p.length+1);}body{
		if(!(i&1)){
			p~=(int[]).init;
			foreach_reverse(j;i/2..p.length-1) p[j+1]=p[j];
			p[i/2]=[];
		}
		p[i/2]~=x;
	}
	void remove(size_t x){
	Lb:foreach(ref y;p){
			foreach(i,z;y){
				if(z==x){
					y=y.remove(i);
					y.assumeSafeAppend();
					break Lb;
				}
			}
		}
		foreach(i,y;p){
			if(!y.length){
				p=p.remove(i);
				p.assumeSafeAppend();
				return;
			}
		}
	}
	void assignRandomly(R)(R r)in{assert(reduce!"a+b"(0,p.map!(a=>cast(int)a.length))==r.length,text(r,p));}body{
		int[] s;
		bool hasDuplicates(int[] s){
			foreach(i;1..s.length) if(s[i-1]==s[i]) return true;
			return false;
		}
		do{
			s=iota(p.length).map!(_=>construct!int()).array;
			s.sort();
		}while(hasDuplicates(s));
		foreach(j,x;p){
			foreach(i;x) r[i]=s.front;
			s.popFront();
		}
	}
	size_t getIndex(int x){
		foreach(i;0..p.length){
			assert(p[i].length);
			if(x<p[i][0]) return 2*i;
			if(x==p[i][0]) return 2*i+1;
		}
		return 2*p.length;
	}
	auto dup(){ return OrderedPartition(p.map!(a=>a.array).array); }

	// TODO: more efficient representation?
	int[][] p;
}

/+enum lowSuffix=(delegate string(int i)=>
				(i>10?__traits(parent,{})(i/10):"")
				~ text("₀₁₂₃₄₅₆₇₈₉"d[i%10]));+/

string lowSuffix(int i){ return (i>10?lowSuffix(i/10):"") ~ text("₀₁₂₃₄₅₆₇₈₉"d[i%10]); }

struct uQueue(T){
	T[] e;
	size_t size(){ return e.length; }
	size_t cap=0;
	void push(T t){
		e~=t;
	}
	T pop()in{ assert(size());}body{
		auto r=e[0];
		e=e[1..$];
		if(++cap>e.length){ // TODO: ok?
			cap=0;
			e=e.dup;
		}
		return r;
	}
}

struct Heap(T,alias comp=(a,b)=>a<b){
	T[] e; // TODO: contiguous storage suitable for this use case?
	size_t size(){ return e.length; }
	void push(T t){
		e~=t;
		for(auto i=e.length-1;i;i=i-1>>1)
			if(comp(e[i],e[i-1>>1]))
				swap(e[i-1>>1],e[i]);
	}
	T pop()in{ assert(size()); }body{
		auto r=e[0];
		swap(e[0],e[$-1]);
		e=e[0..$-1];
		e.assumeSafeAppend();
		for(size_t i=0;2*i+1<e.length;){
			auto j=1+(2*i+2>=e.length||comp(e[2*i+1],e[2*i+2]));
			if(comp(e[2*i+j],e[i])){
				swap(e[2*i+j],e[i]);
				i=2*i+j;
			}else break;
		}
		return r;
	}
}

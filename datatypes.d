module datatypes;
import std.conv, std.random;

import annotations;

struct Set(T){
	void[0][T] elems;
	bool opEquals(Set rhs){ return elems==rhs.elems; }
	Set clone(){
		void[0][T] nelems;
		foreach(k,v;elems) nelems[k]=v;
		return Set(nelems);
	}
	string toString(){
		string r="{";
		foreach(k,_;elems) r~=k.to!string()~", ";
		r~="}";
		return r;
	}

	bool contains(T e){ return !!(e in elems); }
	bool add(T e){ auto r=contains(e); elems[e]=[]; return !r; }
	bool remove(T e){ auto r=contains(e); elems.remove(e); return r; }
	int size(){ return cast(int)elems.length; }
}

struct Map(K,V){
	V[K] elems;
	bool opEquals(Map rhs){ return elems==rhs.elems; }
	Map clone(){
		V[K] nelems;
		foreach(k,v;elems) nelems[k]=v;
		return Map(nelems);
	}
	string toString(){
		string r="{";
		foreach(k,v;elems) r~=k.to!string()~" → "~v.to!string()~", ";
		r~="}";
		return r;
	}

	V get(K key){ return elems.get(key,V.init); }
	V put(K key, V value){ auto r=get(key); elems[key]=value; return r; }
	// V remove(K key){ auto r=get(key); elems.remove(key); return r; }
	// int size(){ return cast(int)elems.length; }
}

struct MultiSet(T){
	int[T] elems;
	bool opEquals(MultiSet rhs){ return elems==rhs.elems; }
	MultiSet clone(){
		int[T] nelems;
		foreach(k,v;elems) nelems[k]=v;
		return MultiSet(nelems,siz);
	}
	string toString(){
		string r="{";
		foreach(k,v;elems){
			foreach(i;0..v)
				r~=k.to!string()~", ";
		}
		r~="}";
		return r;
	}
	
	// bool has(T e){ return !!(e in elems); } // has and remove do not satisfy the soundness property
	int num(T e){ return elems.get(e,0); }
	bool add(T e){ auto r=!!(e in elems); siz++; elems[e]=num(e)+1; return !r; }
	bool remove(T e){
		auto r=!!(e in elems);
		if(r){
			elems[e]--;
			siz--;
			if(!elems[e])
				elems.remove(e);
		}
		return r;
	}
	int size(){ return siz; }
//private:
	int siz=0;
}

struct MaxRegister(T){
	T value;
	MaxRegister clone(){ return this; }
	string toString(){ return "["~value.to!string~"]"; }
	T get(){ return value; }
	T set(T v){ auto r=value; if(v>value) value=v; return r; }
}

int construct(T)(int lower=int.min,int upper=int.max)if(is(T==int)){
	if(lower>=upper) upper=lower+1; // TODO: ok?
	static int[] values;
	if(lower==int.min&&upper==int.max){
		if(values.length&&!uniform(0,10)) return values[uniform(0,$)];
	}
	if(values.length>100){ values.length=0; values.assumeSafeAppend(); }
	values~=uniform!"[)"(max(lower,-100),min(upper,101));
	return values[$-1];
}
bool construct(T)()if(is(T==bool)){ return !!uniform(0,2); }

import std.algorithm: min, max;

struct RangeUpdate{
	auto clone(){ return RangeUpdate(data.dup); }
	bool opEquals(RangeUpdate rhs){ return data==rhs.data; }
	bool add2(int l,int r){
		if(!data.length) data=new int[100];
		if(l<0||r>=data.length/+||r<l+/) return false;
		foreach(i;l..r+1) data[i]+=2;
		return true;
	}
	bool square(int l,int r){
		if(!data.length) data=new int[100];
		if(l<0||r>=data.length/+||r<l+/) return false;
		foreach(i;l..r+1) data[i]^^=2;
		return true;
	}
//private:
	int[] data;
}

int dist(int a,int b){ return a>b?a-b:b-a; }
// @useFunction!dist
struct KDTree(T){ // (dummy implementation)
	KDTree clone(){ return KDTree(data.dup); }
	//bool opEquals(KDTree rhs){ return data==rhs.data; }
	@either!("t",useDefault!"t",sampleFrom!("t","data"))
	bool add(T t){
		auto len=data.length;
		data~=t;
		import std.algorithm, std.array;
		data=data.sort.uniq.array;
		return data.length>len;
	}
	@either!("t",useDefault!"t",sampleFrom!("t","data"))
	bool remove(T t){
		auto len=data.length;
		foreach(i,x;data)
			if(x==t){
				foreach(j;i+1..data.length)
					data[j-1]=data[j];
				import std.array;
				data.popBack();
				data.assumeSafeAppend();
				break;
			}
		return data.length<len; // TODO: support void
	}
	@either!("t",useDefault!"t",sampleFrom!("t","data"))
	T nearest(T t){
		T min=dist(data[0],t);
		T near=data[0]; // (will crash sometimes)
		foreach(x;data[1..$]){
			auto nm=dist(x,t);
			if(nm<min){
				min=nm;
				near=x;
			}
		}
		return near;
	}

	T[] data;
}

// cannot do those yet:

struct ArrayList(T){
	auto clone(){ return ArrayList(data.dup); }

	@bounded!("i",`0`,`cast(int)data.length+1`)
	void add_at(int i,T v){
		data.length++;
		foreach_reverse(j;i..data.length-1)
			data[j+1]=data[j];
		data[i]=v;
	}
	@bounded!("i",`0`,`cast(int)data.length`)
	int get(int i){ return data[i]; }

	@either!("v",sampleFrom!("v","data"),bounded!("v",`-10`,`11`))
	int indexOf(int v){
		foreach(i,x;data) if(v==x) return cast(int)i;
		return -1;
	}	

	@either!("v",sampleFrom!("v","data"),bounded!("v",`-10`,`11`))
	int lastIndexOf(int v){
		foreach_reverse(i,x;data) if(v==x) return cast(int)i;
		return -1;
	}

	@bounded!("i",`0`,`cast(int)data.length`)
	void remove_at(int i){
		foreach(j;i..data.length-1)
			data[j]=data[j+1];
		data.length--;
		data.assumeSafeAppend();
	}
	@bounded!("i",`0`,`cast(int)data.length`)
	@bounded!("x",`-10`,`11`)
	T set(int i,T x){
		T r=data[i];
		data[i]=x;
		return r;
	}
	int size(){ return cast(int)data.length; }

	T[] data;
}

struct Accumulator{
	auto clone(){ return this; }
	int value;
	void increase(int v){
		value+=v;
	}
	int read(){ return value; }
}


int findP(int[] p, int x){
	if(p[x]==x) return x;
	return p[x]=findP(p,p[x]);
}


struct UnionFind(string which, bool uniteReturnSuccess=true){
	auto clone(){ return UnionFind(parents.dup, minima.dup); }
	auto opEquals(UnionFind rhs){
		foreach(x;0..cast(int)parents.length)
			if(find(x)!=rhs.find(x)) return false;
		return true;
	}
	void add(){
		parents~=cast(int)parents.length;
		minima~=parents[$-1];
	}
	@bounded!("x",`0`,`cast(int)parents.length`)
	int find(int x){
		auto p=findP(parents,x);
		static if(which=="min") return minima[p];
		else return p;
	}
	@bounded!("a",`0`,`cast(int)parents.length`)
	@bounded!("b",`0`,`cast(int)parents.length`)
	auto unite(int a,int b){
		auto pa=findP(parents,a), pb=findP(parents,b);
		static if(which!="deterministic"){
			import std.algorithm;
			if(uniform(0,2)) swap(pa,pb);
		}
		parents[pb]=parents[pa];
		minima[pa]=min(minima[pa],minima[pb]);
		static if(uniteReturnSuccess) return pa!=pb;
	}
	int[] parents;
	int[] minima;
}

struct VoidTest{
	void foo(int x){}
	void bar(int x){}

	VoidTest clone(){ return this; }
}

struct ExistentialTest{
	int[20] data;
	@bounded!("i","0","cast(int)data.length")
	void put(int i,int x){ data[i]=x; }

	@bounded!("i","0","cast(int)data.length")
	int get(int i){ return data[i]; }
	
	void add2until(int x){
		foreach(ref y;data){
			if(x==y) return;
			y+=2;
			if(y==x) y++;
		}
	}

	void squareFrom(int x){
		bool seen=false;
		foreach(ref y;data){
			if(seen){
				y=y^^2;
				if(y==x) y++;
			}
			if(x==y) seen=true;
		}
		if(!seen){
			foreach(ref y;data){
				y=y^^2;
				if(y==x) y++;
			}
		}
	}

	ExistentialTest clone(){ return this; }
}


struct MultiSetTest(T){
	int[T] elems;
	bool opEquals(MultiSetTest rhs){ return elems==rhs.elems; }
	MultiSetTest clone(){
		int[T] nelems;
		foreach(k,v;elems) nelems[k]=v;
		return MultiSetTest(nelems,siz);
	}
	string toString(){
		string r="{";
		foreach(k,v;elems){
			foreach(i;0..v)
				r~=k.to!string()~", ";
		}
		r~="}";
		return r;
	}
	
	// bool has(T e){ return !!(e in elems); } // has and remove do not satisfy the soundness property
	@bounded!("e","0","10")
	int num(T e){ return elems.get(e,0); }

	@bounded!("e","0","10")
	bool contains(T e){ return num(e)>0; }

	@bounded!("e","0","10")
	void add(T e){ auto r=!!(e in elems); siz++; elems[e]=num(e)+1; }

	@bounded!("e","0","10")
	void remove(T e){
		auto r=!!(e in elems);
		if(r){
			elems[e]--;
			siz--;
			if(!elems[e])
				elems.remove(e);
		}
	}
	int size(){ return siz; }
//private:
	int siz=0;
}

struct SetTest(T){
	void[0][T] elems;
	bool opEquals(SetTest rhs){ return elems==rhs.elems; }
	SetTest clone(){
		void[0][T] nelems;
		foreach(k,v;elems) nelems[k]=v;
		return SetTest(nelems);
	}
	string toString(){
		string r="{";
		foreach(k,_;elems) r~=k.to!string()~", ";
		r~="}";
		return r;
	}

	@bounded!("e","0","10")
	bool contains(T e){ return !!(e in elems); }
	@bounded!("e","0","10")
	void add(T e){ elems[e]=[]; }
	@bounded!("e","0","10")
	void remove(T e){ elems.remove(e); }
	int size(){ return cast(int)elems.length; }
}


/+
struct UndefRegister{
	bool isDefined;
	int value;
	
	bool initialize(){
		bool v=isDefined;
		isDefined=true;
		return v;
	}
	bool update(int x){
		isDefined=true;
		value=x;
		return 
	}
}
+/

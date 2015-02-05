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
	//enum low=-100,up=100;
	import options;
	enum low=intSamplingRange[0],up=intSamplingRange[1]; // !!!
	values~=uniform!"[)"(max(lower,low),min(upper,up+1));
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

import std.algorithm;
struct IntProximityQuery{
	int[] elems;
	void insert(int x){ elems~=x; }
	void remove(int x){
		foreach(i,ref e;elems){
			if(x!=e) continue;
			swap(e,elems[$-1]);
			elems=elems[0..$-1];
			elems.assumeSafeAppend();
		}
	}
	int nextLarger(int x){
		int m=x;
		foreach(e;elems) if(e>x&&(m==x||m>e)) m=e;
		return m;
	}
	int nextSmaller(int x){
		int m=x;
		foreach(e;elems) if(e<x&&(m==x||m<e)) m=e;
		return m;
	}

	bool opEquals(IntProximityQuery rhs){
		return sort(elems)==sort(rhs.elems);
	}
	IntProximityQuery clone(){ return IntProximityQuery(elems.dup); }
}

// inspired by Trek Palmer's dissertation: ////////

struct IntCell{
	int v;
	int get(){ return v; }
	int put(int x){ auto o=v;v=x;return o; }
	void set(int x){ v=x; }
	int putOne(){ return put(1); }
	int putTwo(){ return put(2); }
	void setOne(){ set(1); }
	void setTwo(){ set(2); }
	IntCell clone(){ return this; }
}

struct PartialMap{
	Set!int dom;
	Map!(int,int) map;

	int put(int k,int v){ dom.add(k); return map.put(k,v); }
	@sampleFrom!("k","dom.elems.keys")
	//@precondition!("k","dom.contains(k)")
	Q!(int,"r",bool,"s") get(int k){
		return containsKey(k)?
			Q!(int,"r",bool,"s")(map.get(k),true):
			Q!(int,"r",bool,"s")(0,false);
	}
	bool containsKey(int k){ return dom.contains(k); }
	void remove(int k){ dom.remove(k); map.elems.remove(k); }

	auto clone(){ return PartialMap(dom.clone(),map.clone()); }
	bool opEquals(PartialMap r){
		if(dom!=r.dom) return false;
		foreach(k,_;dom.elems)
			if(map.get(k)!=r.map.get(k))
				return false;
		return true;
	}
	int size(){ return dom.size(); }
}

import std.range;
////////////////////////////////////////////////////
import std.container;
struct Queue{
	DList!int list;
	int l=0;
	int size(){ return l; }
	void push(int x){
		list.insertBack(x);
		l++;
	}
	Q!(int,"r",bool,"s") front(){
		return size()?
			Q!(int,"r",bool,"s")(list.front,true):
			Q!(int,"r",bool,"s")(0,false);
	}
	bool pop(){ if(!size()) return false; l--; list.removeFront(); return true; }

	Queue clone(){ return Queue(list.dup,l); }
	bool opEquals(Queue r){
		return equal(list[],r.list[]);
	}
}

struct Stack{
	int[] a;
	int size(){ return cast(int)a.length; }
	void push(int x){ a~=x; }
	Q!(int,"r",bool,"s") top(){
		return size()?
			Q!(int,"r",bool,"s")(a[$-1],true):
			Q!(int,"r",bool,"s")(0,false);
	}
	bool pop(){ if(!size()) return false; a=a[0..$-1], a.assumeSafeAppend(); return true; }

	Stack clone(){ return Stack(a.dup); }
}

struct MinHeap{
	int[] a;
	int size(){ return cast(int)a.length; }
	void push(int x){ a~=x; sort!"a>b"(a); }
	Q!(int,"r",bool,"s") top(){
		return size()?
			Q!(int,"r",bool,"s")(a[$-1],true):
			Q!(int,"r",bool,"s")(0,false);
	}
	bool pop(){ if(!size()) return false; a=a[0..$-1], a.assumeSafeAppend(); return true; }

	MinHeap clone(){ return MinHeap(a.dup); }
}

import std.typecons : Q=Tuple, q=tuple;
struct LexicographicProximityQuery{
	Q!(int,int)[] elems;
	void insert(int a,int b){
		foreach(x;elems) if(x==q(a,b)) return;
		elems~=q(a,b);
	}
	void remove(int a,int b){
		auto x=q(a,b);
		foreach(i,ref e;elems){
			if(x!=e) continue;
			swap(e,elems[$-1]);
			elems=elems[0..$-1];
			elems.assumeSafeAppend();
			break;
		}
	}
	Q!(int,"c",int,"d") nextLarger(int a,int b){
		Q!(int,"c",int,"d") x=q(a,b), m=x;
		foreach(e;elems) if(e>x&&(m==x||m>e)) m=e;
		return m;
	}
	Q!(int,"c",int,"d") nextSmaller(int a,int b){
		Q!(int,"c",int,"d") x=q(a,b), m=x;
		foreach(e;elems) if(e<x&&(m==x||m<e)) m=e;
		return m;
	}

	bool opEquals(LexicographicProximityQuery rhs){
		return sort(elems)==sort(rhs.elems);
	}
	auto clone(){ return LexicographicProximityQuery(elems.dup); }
}

struct BitList{
	bool[] a;
	@bounded!("i","0","cast(int)a.length")
	bool set(int i,bool x){ auto o=a[i]; a[i]=x; return o; }
	@bounded!("i","0","cast(int)a.length")
	bool get(int i){ return a[i]; }
	int size(){ return cast(int)a.length; }
	@bounded!("x","0","cast(int)a.length+10")
	void resize(int x){ a.length=x; }
	@bounded!("i","0","cast(int)a.length+1")
	void insert(int i,bool x){
		a.length++;
		foreach_reverse(k;i..a.length)
			a[k]=a[k-1];
		a[i]=x;
	}
	@bounded!("i","0","cast(int)a.length")
	void remove(int i){
		foreach(k;i..a.length-1)
			a[i]=a[i+1];
		a.length--;
	}
	int findFirst(bool x){ foreach(i,b;a) if(b==x) return cast(int)i; return -1; }
	int findLast(bool x){ foreach_reverse(i,b;a) if(b==x) return cast(int)i; return -1; }
	void toggleFirst(bool x){ auto i=findFirst(x); if(~i) a[i]=!a[i]; }
	int findClosest(int i,bool x){
		foreach(k;0..max(i+1,a.length-i)){
			if(i>=k&&a[i-k]==x) return cast(int)(i-k);
			if(i+k<a.length&&a[i+k]==x) return cast(int)(i+k);
		}
		return -1;
	}
	void toggleClosest(int i,bool x){ auto j=findClosest(i,x); if(~j) a[j]=!a[j]; }
	void sort(){ .sort(a); }
	@bounded!("s","0","cast(int)a.length")
	@bounded!("e","0","cast(int)a.length+1")
	void invertBlock(int s,int e){
		foreach(i;s..e) a[i]=!a[i];
	}
	@bounded!("s","0","cast(int)a.length")
	@bounded!("e","0","cast(int)a.length+1")
	void reverseBlock(int s,int e){
		foreach(i;s..(e+s)/2) swap(a[i],a[e-1+s-i]);
	}
	@bounded!("s","0","cast(int)a.length")
	@bounded!("e","0","cast(int)a.length+1")
	void shiftBlock(int s,int e){
		foreach(i;s..e) swap(a[i],a[(i-s+1)%(e-s)+s]);
	}
	auto clone(){ return BitList(a.dup); }
}

struct BitTextEditor{
	bool[] text;
	int cursor=0;
	int position(){ return cursor; }
	int length(){ return cast(int)text.length; }
	bool read(){ while(cursor>=text.length) text~=false; return text[cursor]; }
	void insert(bool b){
		text~=b;
		foreach_reverse(i;cursor..text.length-1)
			swap(text[i],text[i+1]);
		cursor++;
	}
	void delRight(){
		moveRight(), delete_();
	}
	void delete_(){
		cursor--;
		if(cursor<0){ cursor=0; return; }
		foreach(i;cursor..text.length-1)
			swap(text[i],text[i+1]);
		text=text[0..$-1];
		text.assumeSafeAppend();
	}
	void moveLeft(){ cursor=max(0,cursor-1); }
	void moveRight(){ cursor++; while(cursor>=text.length) text~=false; }

	auto clone(){ return BitTextEditor(text.dup,cursor); }
}

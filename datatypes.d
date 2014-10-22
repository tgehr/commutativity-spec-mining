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

	bool has(T e){ return !!(e in elems); }
	bool add(T e){ auto r=has(e); elems[e]=[]; return !r; }
	bool remove(T e){ auto r=has(e); elems.remove(e); return r; }
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
	if(values.length&&!uniform(0,10)) return values[uniform(0,$)];
	if(values.length>100){ values.length=0; values.assumeSafeAppend(); }
	values~=uniform!"[)"(max(lower,-100),min(upper,101)); // TODO: ok?
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

// cannot do those yet:

struct ArrayList(T){
	auto clone(){ return ArrayList(data.dup); }
	bool opEquals(ArrayList rhs){ return data==rhs.data; }

	@bounded!("i",`0`,`cast(int)data.length+1`)
	bool add_at(int i,T v){
		data.length++;
		foreach_reverse(j;i..data.length-1)
			data[j+1]=data[j];
		data[i]=v;
		return true; // TODO: support void
	}
	@bounded!("i",`0`,`cast(int)data.length`)
	int get(int i){ return data[i]; }

	@either!("v",sampleFrom!("v","data"),useDefault!"v")
	int indexOf(int v){
		foreach(i,x;data) if(v==x) return cast(int)i;
		return -1;
	}	

	@either!("v",sampleFrom!("v","data"),useDefault!"v")
	int lastIndexOf(int v){
		foreach_reverse(i,x;data) if(v==x) return cast(int)i;
		return -1;
	}

	@bounded!("i",`0`,`cast(int)data.length`)
	bool remove_at(int i){
		foreach(j;i..data.length-1)
			data[j]=data[j+1];
		data.length--;
		data.assumeSafeAppend();
		return true; // TODO: support void
	}
	@bounded!("i",`0`,`cast(int)data.length`)
	T set(int i,T x){
		T r=data[i];
		data[i]=x;
		return r;
	}
	int size(){ return cast(int)data.length; }

	T[] data;
}

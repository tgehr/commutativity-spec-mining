import std.traits,std.random;
import datatypes,util;

@annotation
struct annotation{}


template obtainSamplerFor(alias method, string parameter){
	alias udas=Seq!(__traits(getAttributes,method));
	alias obtainSamplerFor=typeof({
		foreach(i,uda;udas)
			static if(isSamplerFor!(method,parameter,uda)) return uda();
		static if(!is(typeof(return))) return useDefault!parameter();
		assert(0);
	}());
}

template isSamplerFor(alias method, string parameter, alias sampler){
	static if(is(sampler==a!T,alias a,T...)){
		static if(is(typeof(sampler.sample))){
			enum isSamplerFor=T.length>0&&is(typeof(T[0])==string)&&T[0]==parameter;
		}else enum isSamplerFor=false;
	}else enum isSamplerFor=false;
}

@annotation
struct sampler(string parameter,string sampleIt,string possible=`true`){
	bool canSample(T)(ref T d){
		with(d) return mixin(possible);
	}
	auto sample(T,alias method)(ref T d){
		enum parameterType={
			alias pt=ParameterTypeTuple!method;
			alias pi=ParameterIdentifierTuple!method;
			foreach(i,id;pi){
				static if(id==parameter) return pt[i].init;
			}
			assert(0,"no parameter `"~parameter~"` for method `"~__traits(identifier,method)~"`");
		}();
		return{
			mixin("typeof(parameterType) "~parameter~";");
			with(d) return mixin(sampleIt);
		}();
	}
}

@annotation
struct useDefault(string parameter){
	sampler!(parameter,"construct!(typeof("~parameter~"))()") theSampler;
	alias theSampler this;	
}

@annotation
struct either(string parameter,samplers...){ // TODO: constrain?
	auto sample(T,alias method)(ref T d){
		// TODO: canSample
		switch(uniform(0,samplers.length)){
			foreach(i,sampler;samplers)
			case i: return sampler().sample!(T,method)(d);
		default: assert(0);
		}
	}
	bool canSample(T)(ref T d){
		foreach(i,sampler;samplers) if(sampler().canSample(d)) return true;
		return false;
	}
}

@annotation 
struct bounded(string parameter,string lower, string upper){
	sampler!(parameter,"construct!(typeof("~parameter~"))("~lower~","~upper~")",lower~"<"~upper) theSampler;
	auto exhaustive(T)(ref T t){
		import std.range;
		with(t) return iota(mixin(lower),mixin(upper));
	}
	alias theSampler this;
}

@annotation
struct sampleFrom(string parameter,string array){
	auto sample(T,alias method)(ref T d){
		with(d){
			auto _arr35889=mixin(array);
			if(!_arr35889.length) return useDefault!parameter().sample!(T,method)(d);
			return _arr35889[uniform(0,$)];
		}
	}
	bool canSample(T)(ref T d){ with(d) return !!mixin(array).length; }
}

@annotation
struct useFunction(alias a){}


#----------------------------------------------------------------------------------------------------------------------------------------------------

# FROMENTIN-PARIS ALGORITHM (V.3) (this code decides if a braid is $\sigma$-(flip)positive or not) - February 2014.
# Algorithm: "http://dx.doi.org/10.1016/j.jalgebra.2011.09.039" / "https://arxiv.org/pdf/1101.1400.pdf"

# Implementation written by Diego ARCIS (thanks to Jean MICHEL) / 2014.

#----------------------------------------------------------------------------------------------------------------------------------------------------

# This code starts the CHEVIE Package (It's necessary at least the CHEVIE Package V.4 - 2013) in the GAP/Greedy mode.
Print(" -------------------------------------------------------------------------- \n");
LoadPackage("chevie");;
CHEVIE.PrintGarside:=rec(GAP:=true,Greedy:=true);; #It's optional.

#####################################################################################################################################################

# Some preliminary functions:

#----------------------------------------------------------------------------------------------------------------------------------------------------
# "IsPositiveWord" returns "true" if and only if $w$ is strictly positive.
IsPositiveWord:=w->Length(w)>0 and ForAll(w,x->x>=0);
# (Ex. IsPositiveWord([1,2,3,4])=true;).
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "IndexBraidWord" returns the index of a braid word $w$.
IndexBraidWord:=w->1+Maximum(List(w,AbsInt));
# (Ex. IndexBraidWord([2,-4,1,-6,3])=7;).
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "InverseBraidWord" returns a braid word representing $[w]^-1$ for a given braid word $w$.
InverseBraidWord:=w->-Reversed(w);
# (Ex. InverseBraidWord([2,-4,1,-6,3])=[-3,6,-1,4,-2];).
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "DeleteTrivialities" returns a given braid word $w$ without trivial subwords $[x,-x]$.
DeleteTrivialities:=function(w)
		    local u,i,j;
  		    u:=[]; j:=0; i:=1;
  		    while i<=Length(w) do
    			  if j>0 and w[i]=-u[j] then 
			     i:=i+1; j:=j-1;
    			  else 
			     j:=j+1; u[j]:=w[i]; i:=i+1;
    			  fi;
  	   	    od;
  		    return u{[1..j]};
		    end; # (Ex. DeleteTrivialities([1,2,-2,-3,-4,4,5,-6,6,-7])=[1,-3,5,-7];).
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "SimplifyBraidWord" returns a braid word $u$ equivalent to a given braid word $w$ which is simplier that it.
SimplifyBraidWord:=w->AsWord(ApplyFunc(Braid(CoxeterGroupSymmetricGroup(IndexBraidWord(w))),w));
# (Ex SimplifyBraidWord([2,5,-2,4,1])=[1,5,4];).
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "BraidTriangleWord" returns a braid word representative for the braid Garside element $\triangle_n$ of size $n$.
BraidTriangleWord:=n->Concatenation(List([n-1,n-2..1],i->[1..i]));
# (Ex. BraidTriangleWord(5)=[1,2,3,4,1,2,3,1,2,1];).
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "PowerWord" returns the $n$-power $u=w^n$ of a given braid word $w$.
PowerWord:=function(w,n)
  	   if n<0 then 
	      w:=InverseBraidWord(w);n:=-n;
	   fi;
  	   return Concatenation(List([1..n],i->w));
	   end; 
#----------------------------------------------------------------------------------------------------------------------------------------------------

#####################################################################################################################################################

# The main algorithms:

#----------------------------------------------------------------------------------------------------------------------------------------------------
# "AlphaI" returns the longest divisor in the parabolic braid monoid $B_I$ of $b$, and the quotient.
AlphaI:=function(b,I)
	local M,res,i,s;
	M:=b.monoid;
	res:=M.Elt([]);
	i:=1;
	while i<=Length(I) do
	      if M.IsLeftDescending(GarsideAlpha(b),I[i]) then
		 s:=M.Elt([M.atoms[I[i]]]);
		 res:=res*s;
		 b:=s^-1*b;
		 i:=1;
    	      else 
		 i:=i+1;
 	      fi;
  	od;
  	return [res,b];
	end;
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "PhiSplitting" computes the $\Phi_n$-splitting "word" $s$ of a given positive $n$-braid word representative $w$.
# (This algorithm appears in the article "A Simple Algorithm Finding Short Sigma-Definite Representative" of Jean Fromentin and Luis Paris.)
PhiSplitting:=function(w,n)
	      local res,B,I,b;
	      res:=[];
	      B:=Braid(CoxeterGroupSymmetricGroup(n));
	      w:=B(Reversed(w));
	      I:=[1..n-2];
  	      while w.pd>0 or w.elm<>[] do
    		    b:=AlphaI(w,I);
		    w:=b[2];
		    b:=Reversed(AsWord(b[1]));
    	      if 1 in I then 
		 Add(res,b); 
	      else 
		 Add(res,n-b);
	      fi;
    	      I:=n-I;
  	      od;
  	      return Reversed(res);
	      end;
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "PosGarsideFormWordAndIndex" returns a braid word $u$ representing [u] such that $[w]=\triangle_n^{-k}[u]$ for a given positive braid word $w$, and its corresponding index k.
PosGarsideFormWordAndIndex:=function(w,n)
			    local B,k;
  			    if IsPositiveWord(w) or w=[] then 
			       return [w,0];
			    fi;
  			    B:=Braid(CoxeterGroupSymmetricGroup(n)); 
  			    w:=ApplyFunc(B,w);
			    k:=-w.pd;
			    w.pd:=0;
  			    return [AsWord(w),k];
			    end;
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "FroParAlg" returns a $\sigma$-(flip)definite braid word representative $y$ for the braid $[w]$ represented by a given braid word $w$.
# (This algorithm appears in the article "A Simple Algorithm Finding Short Sigma-Definite Representative" of Jean Fromentin and Luis Paris.)
FroParAlg:=function(w)
	   local y,e,k,v,u,t,s,b,T,i;
	   y:=[]; e:=0; k:=1;
	   if w<>[] then
	      #--------------------------------------------------------------------------------------------------------------------------------------
  	      v:=SimplifyBraidWord(w); # v is a simplier braid word equivalent to w;
	      k:=IndexBraidWord(v); # this is the index of [w].
	      # k is the index of [w]=[v], i.e. the minimum value i such that $\sigma_{i-1}$ appears in some braid word representing [v];
	      #--------------------------------------------------------------------------------------------------------------------------------------
	      u:=PosGarsideFormWordAndIndex(v,k); t:=u[2];u:=u[1];
	      # Thus, we have [w]=[T]^{-t}[u], where [T] is the k-Garside element;
	      #--------------------------------------------------------------------------------------------------------------------------------------
	      if t=0 or k=2 then # This is the trivial case.
	         y:=DeleteTrivialities(v);
		 if IsPositiveWord(y)=true then e:=1; else e:=-1; fi;
	      else # t<>0 and k<>2 # i.e. k>2 # This is the non-trivial case.
	           #---------------------------------------------------------------------------------------------------------------------------------
		   s:=PhiSplitting(u,k); b:=Length(s); # s is the \Phi_k-splitting of u of length b;
		   T:=BraidTriangleWord(k); # [T] is the k-Garside element;
		   #---------------------------------------------------------------------------------------------------------------------------------
		   if t>=b-1 then # In this case [v] is \sigma_{k-1}-(flip)negative.
		      e:=-1; i:=2;
		      y:=Concatenation(PowerWord(T,-t+b-1),s[1]);
		      while i<=b do
			    y:=Concatenation(y,Concatenation(PowerWord(T,-1),s[i]));
			    i:=i+1;
		      od;
		   else # t<b-1; # In this case [v]^{-1} is \sigma_{k-1}-(flip)negative, i.e. [v] is \sigma_{k-1}-(flip)positive.
		      #------------------------------------------------------------------------------------------------------------------------------
		      v:=InverseBraidWord(v); # Now we use v:=v^-1 instead of v. (REMARK).
		      u:=PosGarsideFormWordAndIndex(v,k)[1]; t:=PosGarsideFormWordAndIndex(v,k)[2];
		      # Thus, we have [v]=[T]^{-t}[u], where [T] is the k-Garside element;
		      if t=0 then # and k<>2 # This is the trivial case.
			 y:=DeleteTrivialities(InverseBraidWord(v));
			 e:=-1; # It is because w^-1 is positive, hence w is negative. 
		      else # t<>0 then # and k<>2 # This is the nontrivial case.
			 #---------------------------------------------------------------------------------------------------------------------------
			 s:=PhiSplitting(u,k); b:=Length(s); # s is the \Phi_k-splitting of u of length b;
			 if t>=b-1 then # In this case [v] is \sigma_{k-1}-(flip)negative (more specifically [v]=[w]^-1).
			    e:=1; i:=2;
			    y:=Concatenation(PowerWord(T,-t+b-1),s[1]);
			    while i<=b do
				  y:=Concatenation(y,Concatenation(PowerWord(T,-1),s[i]));
				  i:=i+1;
			    od;
			    y:=DeleteTrivialities(InverseBraidWord(y));
			 fi;
			 #---------------------------------------------------------------------------------------------------------------------------
		      fi;
		      #------------------------------------------------------------------------------------------------------------------------------
		   fi;
		   #---------------------------------------------------------------------------------------------------------------------------------
	      fi;
	      #--------------------------------------------------------------------------------------------------------------------------------------
	   fi;
	   return Concatenation([y],[[k-1,e]]);
	   end;

# sgn(e) in { 'positive' , 'negative' };
# y is a braid word representing [w], i.e. [y]=[w];
# Therefore [w] is a \sigma_{k-1}-(flip)sgn(e);

#----------------------------------------------------------------------------------------------------------------------------------------------------

#####################################################################################################################################################

#MESSAGE:

#----------------------------------------------------------------------------------------------------------------------------------------------------
Print(" -------------------------------------------------------------------------- \n");
Print(" -------------------------------------------------------------------------- \n");
Print(" ----------------------- FROMENTIN-PARIS ALGORITHM ------------------------ \n");
Print(" ---------------------------- (February, 2014) ---------------------------- \n");
Print(" -------------------------------------------------------------------------- \n");
Print(" -------------------------------------------------------------------------- \n");
#----------------------------------------------------------------------------------------------------------------------------------------------------

#####################################################################################################################################################

# The following code is the non-split version of the FROMENTIN-PARIS ALGORITHM, i.e. it acts for non-split sigma-definite words.

#####################################################################################################################################################

#----------------------------------------------------------------------------------------------------------------------------------------------------
# "SplitBraidWord" returns the $n$-split of a given braid word $w$, i.e. it sends $\sigma_i$ to $\sigma_{n-i}$. 
SplitBraidWord:=function(w,n)
  		return List(w, function(i) if i>0 then return n-i; else return -n-i; fi; end);
		end;
#----------------------------------------------------------------------------------------------------------------------------------------------------
# "FroParAlgNS" returns a $\sigma$-definite braid word representative $y$ for the braid $[w]$ represented by a given braid word $w$. (NON-SPLIT)
FroParAlgNS:=function(w)
	     local v,k,u,x,a,b,c,y;
	     if w<>[] then
	        v:=SimplifyBraidWord(w);
	        k:=IndexBraidWord(v);
	        u:=SplitBraidWord(v,k); # This is the split-version of w (or more specifically of v).
	        x:=FroParAlg(u);
	        a:=SplitBraidWord(x[1],k); b:=x[2][1]; c:=x[2][2];
		y:=Concatenation([a],[[k-b,c]]);
	     else
		y:=[[],[0,0]];
	     fi;
	     return y;
	     end;
#----------------------------------------------------------------------------------------------------------------------------------------------------

#####################################################################################################################################################

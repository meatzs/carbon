/** VerCors annotation for the computation of the left most leaf of a binary tree, 
  * where one needs to prove that the full ownership of the input tree is retained.
  */

final class Node {
	public int value;
	/*@ resource P() = Perm(value, read); @*/
}

public class Test {
	/*@
	 requires Perm(x.value, write);
	 ensures x.P() ** Perm(x.value, 1\2);
	 @*/
	static Node leftLeaf(Node x) { 
		callee(x);
		return x;
	}

	/*@
	 requires Perm(x.value, 1\2);
	 ensures x.P();
	 @*/
	static void callee(Node x) {
		//@ fold x.P();
	}

	/*@
	 requires Perm(x.value, write);
	 ensures x.P() ** Perm(x.value, 1\2);
	 @*/
	static Node leftLeafInlined(Node x) { 
		//@ fold x.P();
		return x;
	}

}

import java.util.Arrays;

interface IntSet {
  boolean contains (int n);
}

class evenSet implements IntSet {
  public boolean contains (int n) {
  	return n % 2 == 0;
  }
}

class listSet implements IntSet {
  private int[] l;

  public listSet (int[] l) {
  	this.l = l;
  }

  public boolean contains (int n) {
    return Arrays.asList(l).contains(n);
  }
}

interface BoolNatPair {
  boolean fst();
  int snd();
}

class makePair implements BoolNatPair {
  private boolean a;
  private int b;

  public makePair(boolean a, int b) {
    this.a = a;
    this.b = b;
  }

  public boolean fst() {
  	return a;
  }

  public int snd() {
  	return b;
  }
}

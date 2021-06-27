// The second example for the Test Generation paper by Matthias Sleurink.

// Generated output:

// class MainCounterexample {
//     public static void main(String[] args) {
//       example_2 instance = new example_2();
//       instance.fail = true;
//       instance.testing();
//       // Above will be null. But there is a postcondition that claims it is not.
//     }
//   }

// Input:

public class example_2 {
    public boolean fail;

    //@ requires Perm(this.fail, 1);
    //@ ensures \result != null;
    public int[] testing() {
        if (this.fail) {
            int[] a = null;
            return a;
        } else {
            int[] a = new int[] { 1, 2 };
            return a;
        }
    }
}
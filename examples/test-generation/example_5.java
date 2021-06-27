// The fifth example for the Test Generation paper by Matthias Sleurink.

// Generated output:

// class MainCounterexample {
//     public static void main(String[] args) {
//       example_5 instance = new example_5();
//       instance.succeed = false;
//       instance.testing();
//       // Above will be null. But there is a postcondition that claims it is not.
//     }
//   }

// Input:

public class example_5 {
    public boolean succeed;

    //@ requires Perm(this.succeed, 1);
    //@ ensures \result != null;
    public int[] testing() {
        if (this.succeed) {
            int[] a = new int[] { 1, 2 };
            return a;
        } else {
            int[] a = null;
            return a;
        }
    }
}
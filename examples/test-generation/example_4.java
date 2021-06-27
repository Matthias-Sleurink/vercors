// The fourth example for the Test Generation paper by Matthias Sleurink.

// Generated output:

// class MainCounterexample {
//     public static void main(String[] args) {
//       int[] param0 = null;
//       example_4 instance = new example_4();
//       instance.fail = true;
//       instance.testing(param0);
//       // Above will be null. But there is a postcondition that claims it is not.
//     }
//   }

// Input:

public class example_4 {
    public boolean fail;

    //@ requires Perm(this.fail, 1);
    //@ ensures \result != null;
    public int[] testing(int[] inp) {
        if (this.fail) {
            return inp;
        } else {
            int[] a = new int[] { 1, 2 };
            return a;
        }
    }
}
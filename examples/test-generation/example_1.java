// The first example for the Test Generation paper by Matthias Sleurink.

// Generated output:

// class MainCounterexample {
//     public static void main(String[] args) {
//       int[] param0 = null;
//       example_1 instance = new example_1();
//       instance.testing(param0);
//       // Above will be null. But there is a postcondition that claims it is not.
//     }
//   }

// Input:

public class example_1 {

    //@ ensures \result != null;
    public int[] testing(int[] inp) {
        return inp;
    }
}
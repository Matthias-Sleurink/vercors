// The third example for the Test Generation paper by Matthias Sleurink.

// Generated output:

// class MainCounterexample {
//     public static void main(String[] args) {
//       example_3 instance = new example_3();
//       instance.testing();
//       // Above will be null. But there is a postcondition that claims it is not.
//     }
//   }

// Input:

public class example_3 {

    //@ ensures \result != null;
    public int[] testing() {
        int[] result = null;
        return result;
    }
}
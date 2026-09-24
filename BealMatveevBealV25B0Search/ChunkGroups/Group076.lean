import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0760
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0761
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0762
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0763
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0764
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0765
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0766
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0767
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0768
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0769

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_076 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 76 + i)) (500 * (10 * 76 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0760
  by_cases h1 : i = 1
  · subst i
    exact chunk_0761
  by_cases h2 : i = 2
  · subst i
    exact chunk_0762
  by_cases h3 : i = 3
  · subst i
    exact chunk_0763
  by_cases h4 : i = 4
  · subst i
    exact chunk_0764
  by_cases h5 : i = 5
  · subst i
    exact chunk_0765
  by_cases h6 : i = 6
  · subst i
    exact chunk_0766
  by_cases h7 : i = 7
  · subst i
    exact chunk_0767
  by_cases h8 : i = 8
  · subst i
    exact chunk_0768
  by_cases h9 : i = 9
  · subst i
    exact chunk_0769
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

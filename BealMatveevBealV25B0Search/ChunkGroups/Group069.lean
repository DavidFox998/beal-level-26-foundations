import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0690
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0691
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0692
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0693
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0694
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0695
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0696
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0697
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0698
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0699

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_069 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 69 + i)) (500 * (10 * 69 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0690
  by_cases h1 : i = 1
  · subst i
    exact chunk_0691
  by_cases h2 : i = 2
  · subst i
    exact chunk_0692
  by_cases h3 : i = 3
  · subst i
    exact chunk_0693
  by_cases h4 : i = 4
  · subst i
    exact chunk_0694
  by_cases h5 : i = 5
  · subst i
    exact chunk_0695
  by_cases h6 : i = 6
  · subst i
    exact chunk_0696
  by_cases h7 : i = 7
  · subst i
    exact chunk_0697
  by_cases h8 : i = 8
  · subst i
    exact chunk_0698
  by_cases h9 : i = 9
  · subst i
    exact chunk_0699
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0900
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0901
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0902
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0903
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0904
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0905
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0906
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0907
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0908
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0909

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_090 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 90 + i)) (500 * (10 * 90 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0900
  by_cases h1 : i = 1
  · subst i
    exact chunk_0901
  by_cases h2 : i = 2
  · subst i
    exact chunk_0902
  by_cases h3 : i = 3
  · subst i
    exact chunk_0903
  by_cases h4 : i = 4
  · subst i
    exact chunk_0904
  by_cases h5 : i = 5
  · subst i
    exact chunk_0905
  by_cases h6 : i = 6
  · subst i
    exact chunk_0906
  by_cases h7 : i = 7
  · subst i
    exact chunk_0907
  by_cases h8 : i = 8
  · subst i
    exact chunk_0908
  by_cases h9 : i = 9
  · subst i
    exact chunk_0909
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

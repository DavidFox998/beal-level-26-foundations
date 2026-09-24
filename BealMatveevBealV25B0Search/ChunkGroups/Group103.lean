import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1030
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1031
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1032
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1033
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1034
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1035
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1036
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1037
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1038
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1039

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_103 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 103 + i)) (500 * (10 * 103 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1030
  by_cases h1 : i = 1
  · subst i
    exact chunk_1031
  by_cases h2 : i = 2
  · subst i
    exact chunk_1032
  by_cases h3 : i = 3
  · subst i
    exact chunk_1033
  by_cases h4 : i = 4
  · subst i
    exact chunk_1034
  by_cases h5 : i = 5
  · subst i
    exact chunk_1035
  by_cases h6 : i = 6
  · subst i
    exact chunk_1036
  by_cases h7 : i = 7
  · subst i
    exact chunk_1037
  by_cases h8 : i = 8
  · subst i
    exact chunk_1038
  by_cases h9 : i = 9
  · subst i
    exact chunk_1039
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

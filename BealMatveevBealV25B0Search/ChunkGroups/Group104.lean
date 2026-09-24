import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1040
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1041
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1042
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1043
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1044
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1045
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1046
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1047
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1048
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1049

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_104 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 104 + i)) (500 * (10 * 104 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1040
  by_cases h1 : i = 1
  · subst i
    exact chunk_1041
  by_cases h2 : i = 2
  · subst i
    exact chunk_1042
  by_cases h3 : i = 3
  · subst i
    exact chunk_1043
  by_cases h4 : i = 4
  · subst i
    exact chunk_1044
  by_cases h5 : i = 5
  · subst i
    exact chunk_1045
  by_cases h6 : i = 6
  · subst i
    exact chunk_1046
  by_cases h7 : i = 7
  · subst i
    exact chunk_1047
  by_cases h8 : i = 8
  · subst i
    exact chunk_1048
  by_cases h9 : i = 9
  · subst i
    exact chunk_1049
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

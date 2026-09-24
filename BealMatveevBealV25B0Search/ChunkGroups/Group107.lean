import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1070
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1071
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1072
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1073
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1074
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1075
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1076
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1077
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1078
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1079

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_107 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 107 + i)) (500 * (10 * 107 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1070
  by_cases h1 : i = 1
  · subst i
    exact chunk_1071
  by_cases h2 : i = 2
  · subst i
    exact chunk_1072
  by_cases h3 : i = 3
  · subst i
    exact chunk_1073
  by_cases h4 : i = 4
  · subst i
    exact chunk_1074
  by_cases h5 : i = 5
  · subst i
    exact chunk_1075
  by_cases h6 : i = 6
  · subst i
    exact chunk_1076
  by_cases h7 : i = 7
  · subst i
    exact chunk_1077
  by_cases h8 : i = 8
  · subst i
    exact chunk_1078
  by_cases h9 : i = 9
  · subst i
    exact chunk_1079
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1060
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1061
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1062
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1063
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1064
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1065
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1066
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1067
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1068
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1069

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_106 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 106 + i)) (500 * (10 * 106 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1060
  by_cases h1 : i = 1
  · subst i
    exact chunk_1061
  by_cases h2 : i = 2
  · subst i
    exact chunk_1062
  by_cases h3 : i = 3
  · subst i
    exact chunk_1063
  by_cases h4 : i = 4
  · subst i
    exact chunk_1064
  by_cases h5 : i = 5
  · subst i
    exact chunk_1065
  by_cases h6 : i = 6
  · subst i
    exact chunk_1066
  by_cases h7 : i = 7
  · subst i
    exact chunk_1067
  by_cases h8 : i = 8
  · subst i
    exact chunk_1068
  by_cases h9 : i = 9
  · subst i
    exact chunk_1069
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

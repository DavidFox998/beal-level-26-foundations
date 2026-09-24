import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0090
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0091
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0092
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0093
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0094
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0095
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0096
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0097
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0098
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0099

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_009 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 9 + i)) (500 * (10 * 9 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0090
  by_cases h1 : i = 1
  · subst i
    exact chunk_0091
  by_cases h2 : i = 2
  · subst i
    exact chunk_0092
  by_cases h3 : i = 3
  · subst i
    exact chunk_0093
  by_cases h4 : i = 4
  · subst i
    exact chunk_0094
  by_cases h5 : i = 5
  · subst i
    exact chunk_0095
  by_cases h6 : i = 6
  · subst i
    exact chunk_0096
  by_cases h7 : i = 7
  · subst i
    exact chunk_0097
  by_cases h8 : i = 8
  · subst i
    exact chunk_0098
  by_cases h9 : i = 9
  · subst i
    exact chunk_0099
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

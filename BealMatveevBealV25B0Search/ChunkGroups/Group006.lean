import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0060
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0061
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0062
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0063
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0064
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0065
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0066
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0067
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0068
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0069

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_006 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 6 + i)) (500 * (10 * 6 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0060
  by_cases h1 : i = 1
  · subst i
    exact chunk_0061
  by_cases h2 : i = 2
  · subst i
    exact chunk_0062
  by_cases h3 : i = 3
  · subst i
    exact chunk_0063
  by_cases h4 : i = 4
  · subst i
    exact chunk_0064
  by_cases h5 : i = 5
  · subst i
    exact chunk_0065
  by_cases h6 : i = 6
  · subst i
    exact chunk_0066
  by_cases h7 : i = 7
  · subst i
    exact chunk_0067
  by_cases h8 : i = 8
  · subst i
    exact chunk_0068
  by_cases h9 : i = 9
  · subst i
    exact chunk_0069
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

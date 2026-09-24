import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1980
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1981
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1982
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1983
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1984
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1985
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1986
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1987
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1988
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1989

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_198 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 198 + i)) (500 * (10 * 198 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1980
  by_cases h1 : i = 1
  · subst i
    exact chunk_1981
  by_cases h2 : i = 2
  · subst i
    exact chunk_1982
  by_cases h3 : i = 3
  · subst i
    exact chunk_1983
  by_cases h4 : i = 4
  · subst i
    exact chunk_1984
  by_cases h5 : i = 5
  · subst i
    exact chunk_1985
  by_cases h6 : i = 6
  · subst i
    exact chunk_1986
  by_cases h7 : i = 7
  · subst i
    exact chunk_1987
  by_cases h8 : i = 8
  · subst i
    exact chunk_1988
  by_cases h9 : i = 9
  · subst i
    exact chunk_1989
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

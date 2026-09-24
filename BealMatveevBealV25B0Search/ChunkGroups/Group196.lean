import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1960
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1961
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1962
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1963
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1964
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1965
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1966
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1967
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1968
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1969

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_196 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 196 + i)) (500 * (10 * 196 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1960
  by_cases h1 : i = 1
  · subst i
    exact chunk_1961
  by_cases h2 : i = 2
  · subst i
    exact chunk_1962
  by_cases h3 : i = 3
  · subst i
    exact chunk_1963
  by_cases h4 : i = 4
  · subst i
    exact chunk_1964
  by_cases h5 : i = 5
  · subst i
    exact chunk_1965
  by_cases h6 : i = 6
  · subst i
    exact chunk_1966
  by_cases h7 : i = 7
  · subst i
    exact chunk_1967
  by_cases h8 : i = 8
  · subst i
    exact chunk_1968
  by_cases h9 : i = 9
  · subst i
    exact chunk_1969
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

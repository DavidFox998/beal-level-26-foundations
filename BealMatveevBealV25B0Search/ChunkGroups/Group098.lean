import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0980
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0981
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0982
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0983
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0984
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0985
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0986
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0987
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0988
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0989

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_098 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 98 + i)) (500 * (10 * 98 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0980
  by_cases h1 : i = 1
  · subst i
    exact chunk_0981
  by_cases h2 : i = 2
  · subst i
    exact chunk_0982
  by_cases h3 : i = 3
  · subst i
    exact chunk_0983
  by_cases h4 : i = 4
  · subst i
    exact chunk_0984
  by_cases h5 : i = 5
  · subst i
    exact chunk_0985
  by_cases h6 : i = 6
  · subst i
    exact chunk_0986
  by_cases h7 : i = 7
  · subst i
    exact chunk_0987
  by_cases h8 : i = 8
  · subst i
    exact chunk_0988
  by_cases h9 : i = 9
  · subst i
    exact chunk_0989
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

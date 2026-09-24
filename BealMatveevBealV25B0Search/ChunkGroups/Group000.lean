import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0000
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0001
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0002
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0003
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0004
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0005
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0006
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0007
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0008
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0009

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_000 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 0 + i)) (500 * (10 * 0 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0000
  by_cases h1 : i = 1
  · subst i
    exact chunk_0001
  by_cases h2 : i = 2
  · subst i
    exact chunk_0002
  by_cases h3 : i = 3
  · subst i
    exact chunk_0003
  by_cases h4 : i = 4
  · subst i
    exact chunk_0004
  by_cases h5 : i = 5
  · subst i
    exact chunk_0005
  by_cases h6 : i = 6
  · subst i
    exact chunk_0006
  by_cases h7 : i = 7
  · subst i
    exact chunk_0007
  by_cases h8 : i = 8
  · subst i
    exact chunk_0008
  by_cases h9 : i = 9
  · subst i
    exact chunk_0009
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0960
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0961
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0962
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0963
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0964
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0965
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0966
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0967
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0968
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0969

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_096 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 96 + i)) (500 * (10 * 96 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0960
  by_cases h1 : i = 1
  · subst i
    exact chunk_0961
  by_cases h2 : i = 2
  · subst i
    exact chunk_0962
  by_cases h3 : i = 3
  · subst i
    exact chunk_0963
  by_cases h4 : i = 4
  · subst i
    exact chunk_0964
  by_cases h5 : i = 5
  · subst i
    exact chunk_0965
  by_cases h6 : i = 6
  · subst i
    exact chunk_0966
  by_cases h7 : i = 7
  · subst i
    exact chunk_0967
  by_cases h8 : i = 8
  · subst i
    exact chunk_0968
  by_cases h9 : i = 9
  · subst i
    exact chunk_0969
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

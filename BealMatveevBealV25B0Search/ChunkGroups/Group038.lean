import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0380
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0381
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0382
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0383
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0384
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0385
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0386
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0387
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0388
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0389

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_038 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 38 + i)) (500 * (10 * 38 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0380
  by_cases h1 : i = 1
  · subst i
    exact chunk_0381
  by_cases h2 : i = 2
  · subst i
    exact chunk_0382
  by_cases h3 : i = 3
  · subst i
    exact chunk_0383
  by_cases h4 : i = 4
  · subst i
    exact chunk_0384
  by_cases h5 : i = 5
  · subst i
    exact chunk_0385
  by_cases h6 : i = 6
  · subst i
    exact chunk_0386
  by_cases h7 : i = 7
  · subst i
    exact chunk_0387
  by_cases h8 : i = 8
  · subst i
    exact chunk_0388
  by_cases h9 : i = 9
  · subst i
    exact chunk_0389
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

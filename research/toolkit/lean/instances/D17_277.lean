import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 277 of the cap-17 certificate: slots 141824 .. 142335 -/
theorem chk_277 : chunkCheck 17 T stdSt 141824 512 = true := by decide +kernel

end Row17

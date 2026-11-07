import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 198 of the cap-17 certificate: slots 101376 .. 101887 -/
theorem chk_198 : chunkCheck 17 T stdSt 101376 512 = true := by decide +kernel

end Row17

import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 323 of the cap-17 certificate: slots 165376 .. 165887 -/
theorem chk_323 : chunkCheck 17 T stdSt 165376 512 = true := by decide +kernel

end Row17

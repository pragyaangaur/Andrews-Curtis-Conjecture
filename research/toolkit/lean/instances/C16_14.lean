import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 14 of the cap-16 certificate: slots 14336 .. 15359 -/
theorem chk_14 : chunkCheck 16 T stdSt 14336 1024 = true := by decide +kernel

end Row16

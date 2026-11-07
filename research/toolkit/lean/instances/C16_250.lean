import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 250 of the cap-16 certificate: slots 256000 .. 257023 -/
theorem chk_250 : chunkCheck 16 T stdSt 256000 1024 = true := by decide +kernel

end Row16

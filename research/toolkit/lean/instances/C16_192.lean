import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 192 of the cap-16 certificate: slots 196608 .. 197631 -/
theorem chk_192 : chunkCheck 16 T stdSt 196608 1024 = true := by decide +kernel

end Row16

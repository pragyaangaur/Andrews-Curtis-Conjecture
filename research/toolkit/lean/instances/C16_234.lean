import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 234 of the cap-16 certificate: slots 239616 .. 240639 -/
theorem chk_234 : chunkCheck 16 T stdSt 239616 1024 = true := by decide +kernel

end Row16

namespace ConRon.Arena

/-- DESIGN §8.2's join point. -/
def checkDecl (pd : IDeclaration) : AM Unit := pure ()

/-- The fold over the stream. -/
def checkDeclsPure (ds : List IDeclaration) : AM Unit := pure ()

end ConRon.Arena

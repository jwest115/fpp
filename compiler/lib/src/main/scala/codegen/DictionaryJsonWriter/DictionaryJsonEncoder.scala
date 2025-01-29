package fpp.compiler.codegen

import fpp.compiler.ast._
import fpp.compiler.util._
import fpp.compiler.analysis._
import io.circe._
import io.circe.syntax._



/** ====================================================================== 
 *  Case class representing dictionary metadata
 *  ====================================================================== */
case class DictionaryMetadata(
    deploymentName: String = "[no value specified]",
    projectVersion: String = "[no value specified]", 
    frameworkVersion: String = "[no value specified]", 
    libraryVersions: List[String] = Nil, 
    dictionarySpecVersion: String = "[no value specified]"
)

/** ====================================================================== 
 *  Generate dictionary JSON
 *  ====================================================================== */

case class DictionaryJsonEncoder(
    /** Constructed Dictionary data structure */
    dictionary: Dictionary,
    /** Dictionary State */
    dictionaryState: DictionaryJsonEncoderState
) {
    /** Dictionary entry map to JSON */
    private def dictionaryEntryMapAsJson[A, B] (f1: (A, B) => Json) (map: Map[A, B]): Json =
        (map.map { case (key, value) => f1(key, value) }).toList.asJson

    /** Dictionary symbol set to JSON */
    private def dictionarySymbolSetAsJson[A] (f1: A => Json) (set: Set[A]): Json =
        (set.map(elem => f1(elem))).toList.asJson
    
    /** Enum Constant JSON Encoding */
    private def enumConstantAsJson(aNode: AstNode[Ast.DefEnumConstant]): Map[String, Json] = {
        val Value.EnumConstant(value, _) = dictionaryState.a.valueMap(aNode.id)
        Map(value._1 -> value._2.asJson)
    }

    /** Symbol JSON Encoding */
    private implicit def typeSymbolSetEncoder [T <: Symbol]: Encoder[Set[T]] = {
        def f1(symbol: T) = symbol.asJson
        Encoder.instance (dictionarySymbolSetAsJson (f1) _)
    }

    /** DictionaryMetadata JSON Encoding */
    private implicit def dictionaryMetadataEncoder: Encoder[DictionaryMetadata] = new Encoder[DictionaryMetadata] {
        override def apply(metadata: DictionaryMetadata): Json = {
            Json.obj(
                "deploymentName" -> metadata.deploymentName.asJson,
                "projectVersion" -> metadata.projectVersion.asJson,
                "frameworkVersion" -> metadata.frameworkVersion.asJson,
                "libraryVersions" -> metadata.libraryVersions.asJson,
                "dictionarySpecVersion" -> metadata.dictionarySpecVersion.asJson
            )
        }
    }

    /** JSON Encoding for Maps of Commands, Parameters, Events, Telemetry Channels, Records, and Containers */
    private implicit val commandMapEncoder: Encoder[Map[BigInt, CommandEntry]] = {
        def f1(opcode: BigInt, command: CommandEntry) = (opcode -> command).asJson
        Encoder.instance (dictionaryEntryMapAsJson (f1) _)
    }

    private implicit val paramMapEncoder: Encoder[Map[BigInt, ParamEntry]] = {
        def f1(identifier: BigInt, param: ParamEntry) = (identifier -> param).asJson
        Encoder.instance (dictionaryEntryMapAsJson (f1) _)
    }

    private implicit val eventMapEncoder: Encoder[Map[BigInt, EventEntry]] = {
        def f1(identifier: BigInt, event: EventEntry) = (identifier -> event).asJson
        Encoder.instance (dictionaryEntryMapAsJson (f1) _)
    }

    private implicit val channelMapEncoder: Encoder[Map[BigInt, TlmChannelEntry]] = {
        def f1(identifier: BigInt, event: TlmChannelEntry) = (identifier -> event).asJson
        Encoder.instance (dictionaryEntryMapAsJson (f1) _)
    }

    private implicit val recordMapEncoder: Encoder[Map[BigInt, RecordEntry]] = {
        def f1(identifier: BigInt, record: RecordEntry) = (identifier -> record).asJson
        Encoder.instance (dictionaryEntryMapAsJson (f1) _)
    }

    private implicit val containerMapEncoder: Encoder[Map[BigInt, ContainerEntry]] = {
        def f1(identifier: BigInt, container: ContainerEntry) = (identifier -> container).asJson
        Encoder.instance (dictionaryEntryMapAsJson (f1) _)
    }

    /** JSON Encoding for FPP Types */
    def typeAsJson[T <: Type](elemType: T): Json = {
        elemType match {
            case Type.PrimitiveInt(kind) => {
                val kindString = kind.toString
                val size = if (kindString.startsWith("I")) kindString.split("I").tail else kindString.split("U").tail
                val signed = if (kindString.startsWith("I")) true else false
                Json.obj(
                    "name" -> kindString.asJson,
                    "kind" -> "integer".asJson,
                    "size" -> size.mkString("").toInt.asJson,
                    "signed" -> signed.asJson
                )
            }
            case Type.Float(kind) => {
                val kindString = kind.toString
                val size = kindString.split("F").tail
                Json.obj(
                    "name" -> kindString.asJson,
                    "kind" -> "float".asJson,
                    "size" -> size.mkString("").toInt.asJson
                )
            }
            case Type.Boolean => Json.obj("name" -> "bool".asJson, "kind" -> "bool".asJson, "size" -> dictionaryState.boolSize.asJson)
            case Type.String(size) => {
                val jsonObj = Json.obj(
                    "name" -> "string".asJson,
                    "kind" -> "string".asJson
                )
                size match {
                    case Some(s) => Json.obj("size" -> valueAsJson(dictionaryState.a.valueMap(s.id))).deepMerge(jsonObj)
                    case None => Json.obj("size" -> dictionaryState.defaultStringSize.asJson).deepMerge(jsonObj)
                }
            }
            case Type.Array(node, _, _, _) => {
                Json.obj(
                    "name" -> dictionaryState.a.getQualifiedName(Symbol.Array(node)).toString.asJson,
                    "kind" -> "qualifiedIdentifier".asJson,
                )
            }
            case Type.Enum(node, _, _) => {
                Json.obj(
                    "name" -> dictionaryState.a.getQualifiedName(Symbol.Enum(node)).toString.asJson,
                    "kind" -> "qualifiedIdentifier".asJson,
                )
            }
            case Type.Struct(node, _, _, _, _) => {
                Json.obj(
                    "name" -> dictionaryState.a.getQualifiedName(Symbol.Struct(node)).toString.asJson,
                    "kind" -> "qualifiedIdentifier".asJson,
                )
            }
            // Case where type we are trying to convert to JSON is not supported in the dictionary spec (should never occur)
            case _ => throw InternalError("type not supported in JSON dictionary spec")
        }
    }

    /** JSON Encoding for arrays */
    def arrayElementsAsJson(elements: List[Value]): Json = {
        val arrayRes = for(e <- elements) yield {
            val res = e match {
                // Case where array is N-dimensional
                case Value.Array(a, t) => arrayElementsAsJson(a.elements)
                case _ => valueAsJson(e)
            }

            res.asJson
        }
        arrayRes.asJson
    }
    
    /** JSON Encoding for FPP Values 
     * 
     * Note: EnumConstants values return the string representation of the constant (not the numeral value)
    */
    def valueAsJson[V <: Value](value: V): Json = {
        value match {
            case Value.PrimitiveInt(v, _) => v.asJson
            case Value.Integer(v) => v.asJson
            case Value.Float(v, _) => v.asJson
            case Value.Boolean(v) => v.asJson
            case Value.String(v) => v.asJson
            case Value.Array(a, t) => arrayElementsAsJson(a.elements)
            case Value.EnumConstant(v, t) => {
                val qualifiedName = dictionaryState.a.getQualifiedName(Symbol.Enum(t.node)).toString
                s"${qualifiedName}.${v._1}".asJson // FQN of the enum constant
            }
            case Value.Struct(Value.AnonStruct(members), t) => members.map((key, value) => (key.toString -> valueAsJson(value))).asJson
            case _ => value.toString.asJson
        }
    }

    /** JSON Encoding for symbols (arrays, enums, and structs only) */
    private implicit def typeSymbolEncoder [T <: Symbol]: Encoder[T] = new Encoder[T] {
        override def apply(symbol: T): Json = {
            val qualifiedName = dictionaryState.a.getQualifiedName(symbol).toString
            symbol match {
                case Symbol.Array(preA, node, postA) => {
                    val arrayType = dictionaryState.a.typeMap(symbol.getNodeId)
                    val Type.Array(_, anonArray, default, format) = arrayType
                    val defaultJsonList: List[Json]= default match {
                        case Some(defaultVal) => for (elem <- defaultVal._1._1) yield valueAsJson(elem)
                        case None => List.empty[Json]
                    }
                    val json = Json.obj(
                        "kind" -> "array".asJson,
                        "qualifiedName" -> qualifiedName.asJson,
                        "size" -> arrayType.getArraySize.asJson,
                        "elementType" -> typeAsJson(anonArray.eltType),
                        "default" -> defaultJsonList.asJson
                    )
                    val optionalValues = Map(
                        "format" -> node.data.format.map(_.data),
                        "annotation" -> concatAnnotations(preA, postA)
                    )
                    jsonWithOptionalValues(json, optionalValues)
                }
                case Symbol.Enum(preA, node, postA) => {
                    val Type.Enum(_, repType, default) = dictionaryState.a.typeMap(symbol.getNodeId)
                    val enumDefault = default match {
                        case Some(defaultVal) => defaultVal.value._1
                        case None => ""
                    }
                    val enumeratedConstants = node.data.constants.map { case (cPreA, cNode, cPostA) =>
                        val json = Json.obj(
                            "name" -> cNode.data.name.asJson,
                            "value" -> dictionaryState.a.valueMap(cNode.id).asInstanceOf[Value.EnumConstant].value._2.asJson
                        )
                        val optionalValues = Map("annotation" -> concatAnnotations(cPreA, cPostA))
                        jsonWithOptionalValues(json, optionalValues)
                    }
                    val json = Json.obj(
                        "kind" -> "enum".asJson,
                        "qualifiedName" -> qualifiedName.asJson,
                        "representationType" -> typeAsJson(repType),
                        "enumeratedConstants" -> enumeratedConstants.asJson,
                        "default" -> s"${qualifiedName}.${enumDefault}".asJson
                    )
                    val optionalValues = Map(
                        "annotation" -> concatAnnotations(preA, postA), 
                    )
                    jsonWithOptionalValues(json, optionalValues)
                }
                case Symbol.Struct(preA, node, postA) => {
                    val Type.Struct(_, _, default, sizes, _) = dictionaryState.a.typeMap(symbol.getNodeId)
                    val memberFormatMap = node.data.members.flatMap { case (_, memberNode, _) =>
                        memberNode.data.format.map(format => memberNode.data.name -> format.data)
                    }.toMap
                    val memberAnnotationMap = node.data.members.flatMap { case (preA, memberNode, postA) =>
                        val annotation = (preA ++ postA).mkString("\n")
                        if (annotation.isEmpty) None else Some(memberNode.data.name -> annotation)
                    }.toMap
                    val membersFormatted = for(((_, m, _), index) <- node.data.members.zipWithIndex) yield {
                        val json = Json.obj(
                            "type" -> typeAsJson(dictionaryState.a.typeMap(m.data.typeName.id)), 
                            "index" -> index.asJson
                        )
                        val optionalValues = Map(
                            "size" -> sizes.get(m.data.name), 
                            "format" -> memberFormatMap.get(m.data.name), 
                            "annotation" -> memberAnnotationMap.get(m.data.name)
                        )
                        (m.data.name.toString -> jsonWithOptionalValues(json, optionalValues))
                    }
                    val json = Json.obj(
                        "kind" -> "struct".asJson,
                        "qualifiedName" -> qualifiedName.asJson,
                        "members" -> membersFormatted.toMap.asJson,
                    )
                    val optionalValues = Map(
                        "default" -> default, 
                        "annotation" -> concatAnnotations(preA, postA)
                    )
                    jsonWithOptionalValues(json, optionalValues)
                }
                // Case where type symbol we are trying to convert to JSON is not supported in the dictionary spec (should never occur)
                case _ => throw InternalError("type symbol not supported in JSON dictionary spec")
            }
        }
    }

    /** JSON Encoding for parameter SET command formal parameters */
    def formatParamSetCommandParams(typeNameNode: AstNode[Ast.TypeName]): Json = {
        // Convert to list since that is how formal params are represented in the JSON spec
        List.apply(Json.obj(
            "name" -> "val".asJson,
            "type" -> typeAsJson(dictionaryState.a.typeMap(typeNameNode.id)),
            "ref" -> false.asJson
        )).asJson
    }

    /** JSON Encoding for FormalParamList */
    private implicit def formalParamListEncoder: Encoder[Ast.FormalParamList] = new Encoder[Ast.FormalParamList] {
        override def apply(params: Ast.FormalParamList): Json = {
            val paramListJson = for (paramEntry <- params) yield {
                val (preA, elem, postA) = paramEntry
                val AstNode(Ast.FormalParam(kind, name, typeNameNode), _) = elem
                val ref = kind match {
                    case Ast.FormalParam.Ref => true
                    case Ast.FormalParam.Value => false
                }
                val json = Json.obj(
                    "name" -> name.asJson,
                    "type" -> typeAsJson(dictionaryState.a.typeMap(typeNameNode.id)),
                    "ref" -> ref.asJson
                )
                val optionalValues = Map(
                    "annotation" -> concatAnnotations(preA, postA)
                )
                jsonWithOptionalValues(json, optionalValues)
            }
            paramListJson.asJson
        }
    }

    /** JSON Encoding for Commands */
    private implicit def commandEncoder: Encoder[(BigInt, CommandEntry)] = new Encoder[(BigInt, CommandEntry)] {
        override def apply(entry: (BigInt, CommandEntry)): Json = {
            val opcode = entry._1
            val command  = entry._2.command
            val name = s"${entry._2.componentInstance.toString}.${command.getName}"
            command match {
                case Command.NonParam(aNode, kind) => {
                    val (preA, node, postA) = aNode
                    val (commandKind, priority, queueFull) = kind match {
                        case Command.NonParam.Async(priority, queueFull) => ("async", priority, Some(queueFull))
                        case Command.NonParam.Guarded => ("guarded", None, None)
                        case Command.NonParam.Sync => ("sync", None, None)
                    }
                    val formalParams = node.data.params
                    val json = Json.obj(
                        "name" -> name.asJson,
                        "commandKind" -> commandKind.asJson, 
                        "opcode" -> opcode.asJson,
                        "formalParams" -> formalParams.asJson
                    )
                    val optionalValues = Map(
                        "priority" -> priority,
                        "queueFullBehavior" -> queueFull,
                        "annotation" -> concatAnnotations(preA, postA)
                    )
                    jsonWithOptionalValues(json, optionalValues)
                }
                // Case where command is param set/save command
                case fpp.compiler.analysis.Command.Param(aNode, kind) => {
                    val (preA, node, postA) = aNode
                    val (commandKind, formalParams) = kind match {
                        case Command.Param.Set => ("set", formatParamSetCommandParams(node.data.typeName))
                        case Command.Param.Save => ("save", List.empty[String].asJson)
                    }
                    val json = Json.obj(
                        "name" -> name.asJson,
                        "commandKind" -> commandKind.asJson, 
                        "opcode" -> opcode.asJson,
                        "formalParams" -> formalParams
                    )
                    val optionalValues = Map(
                        "annotation" -> concatAnnotations(preA, postA)
                    )
                    jsonWithOptionalValues(json, optionalValues)
                }
            }
        }
    }

    /** JSON Encoding for Parameters */
    private implicit def paramEncoder: Encoder[(BigInt, ParamEntry)] = new Encoder[(BigInt, ParamEntry)] {
        override def apply(entry: (BigInt, ParamEntry)): Json = {
            val numIdentifier = entry._1
            val param = entry._2.param
            val name = s"${entry._2.componentInstance.toString}.${param.getName}"
            val (preA, node, postA) = param.aNode
            val json = Json.obj(
                "name" -> name.asJson,
                "type" -> typeAsJson(param.paramType),
                "id" -> numIdentifier.asJson
            )
            val optionalValues = Map(
                "default" -> param.default,
                "annotation" -> concatAnnotations(preA, postA)
            )
            jsonWithOptionalValues(json, optionalValues)
        }
    }

    /** JSON Encoding for Events */
    private implicit def eventEncoder: Encoder[(BigInt, EventEntry)] = new Encoder[(BigInt, EventEntry)] {
        override def apply(entry: (BigInt, EventEntry)): Json = {
            val event = entry._2.event
            val numIdentifier = entry._1
            val name = s"${entry._2.componentInstance.toString}.${event.getName}"
            val (preA, node, postA) = event.aNode
            val severityStr = node.data.severity match {
                case Ast.SpecEvent.ActivityHigh => "ACTIVITY_HI"
                case Ast.SpecEvent.ActivityLow => "ACTIVITY_LO"
                case Ast.SpecEvent.WarningHigh => "WARNING_HI"
                case Ast.SpecEvent.WarningLow => "WARNING_LO"
                case s => s.toString.toUpperCase.replace(' ', '_')
            }
            val json = Json.obj(
                "name" -> name.asJson,
                "severity" -> severityStr.asJson,
                "formalParams" -> node.data.params.asJson,
                "id" -> numIdentifier.asJson,
                "format" -> node.data.format.data.asJson
            )
            val optionalValues = Map(
                "annotation" -> concatAnnotations(preA, postA),
                "throttle" -> event.throttle
            )
            jsonWithOptionalValues(json, optionalValues)
        }
    }

    /** JSON Encoding for TlmChannel.Limits */
    private implicit def channelLimitEncoder: Encoder[TlmChannel.Limits] = new Encoder[TlmChannel.Limits] {
        override def apply(limits: TlmChannel.Limits): Json = {
            (limits.map { case (limitKind, (id, value)) => limitKind.toString -> valueAsJson(value)}).asJson
        }
    }

    /** JSON Encoding for TlmChannels */
    private implicit def channelEncoder: Encoder[(BigInt, TlmChannelEntry)] = new Encoder[(BigInt, TlmChannelEntry)] {
        override def apply(entry: (BigInt, TlmChannelEntry)): Json = {
            val channel = entry._2.tlmChannel
            val numIdentifier = entry._1
            val name = s"${entry._2.componentInstance.toString}.${channel.getName}"
            val (preA, node, postA) = channel.aNode
            val json = Json.obj(
                "name" -> name.asJson,
                "type" -> typeAsJson(channel.channelType),
                "id" -> numIdentifier.asJson,
                "telemetryUpdate" -> channel.update.toString.asJson
            )
            val optionalValues = Map(
                "format" -> node.data.format.map(_.data),
                "annotation" -> concatAnnotations(preA, postA)
            )
            val jsonWithOptionals = jsonWithOptionalValues(json, optionalValues)

            // If channel high or low limits are specified, add them to the JSON and return the telem channel JSON
            if(!channel.lowLimits.isEmpty || !channel.highLimits.isEmpty) {
                val lowLimitJson = if(!channel.lowLimits.isEmpty) Json.obj("low" -> channel.lowLimits.asJson) else Json.obj()
                val highLimitJson = if(!channel.highLimits.isEmpty) Json.obj("high" -> channel.highLimits.asJson) else Json.obj()
                Json.obj("limits" -> lowLimitJson.deepMerge(highLimitJson)).deepMerge(jsonWithOptionals)
            }
            // No channel limits exist, return the telem channel JSON
            else {
                jsonWithOptionals
            }
        }
    }

    /** JSON Encoding for Records */
    private implicit def recordEncoder: Encoder[(BigInt, RecordEntry)] = new Encoder[(BigInt, RecordEntry)] {
        override def apply(entry: (BigInt, RecordEntry)): Json = {
            val record = entry._2.record
            val numIdentifier = entry._1
            val name = s"${entry._2.componentInstance.toString}.${record.getName}"
            val (preA, node, postA) = record.aNode
            val json = Json.obj(
                "name" -> name.asJson,
                "type" -> typeAsJson(record.recordType),
                "array" -> record.isArray.asJson,
                "id" -> numIdentifier.asJson,
            )
            val optionalValues = Map(
                "annotation" -> concatAnnotations(preA, postA)
            )
            jsonWithOptionalValues(json, optionalValues)
        }
    }

    /** JSON Encoding for Containers */
    private implicit def containerEncoder: Encoder[(BigInt, ContainerEntry)] = new Encoder[(BigInt, ContainerEntry)] {
        override def apply(entry: (BigInt, ContainerEntry)): Json = {
            val container = entry._2.container
            val numIdentifier = entry._1
            val name = s"${entry._2.componentInstance.toString}.${container.getName}"
            val (preA, node, postA) = container.aNode
            val json = Json.obj(
                "name" -> name.asJson,
                "id" -> numIdentifier.asJson,
            )
            val optionalValues = Map(
                "defaultPriority" -> container.defaultPriority,
                "annotation" -> concatAnnotations(preA, postA)
            )
            jsonWithOptionalValues(json, optionalValues)
        }
    }

    /** Main interface for the class. JSON Encoding for a complete dictionary */
    def dictionaryAsJson: Json = {
        /** Split set into individual sets consisting of each symbol type (arrays, enums, structs) */
        val typeDefSymbols = splitTypeSymbolSet(dictionary.typeSymbolSet, Set())
        /** Convert each dictionary element to JSON and return the complete dictionary JSON */
        Json.obj(
            "metadata" -> dictionaryState.metadata.asJson,
            "typeDefinitions" -> typeDefSymbols.asJson,
            "commands" -> dictionary.commandEntryMap.asJson,
            "parameters" -> dictionary.paramEntryMap.asJson,
            "events" -> dictionary.eventEntryMap.asJson,
            "telemetryChannels" -> dictionary.tlmChannelEntryMap.asJson,
            "records" -> dictionary.recordEntryMap.asJson,
            "containers" -> dictionary.containerEntryMap.asJson
        )
    }



    /* ############################  Helpers and utilities ############################ */


    /** JSON Encoding for optional fields */
    def jsonWithOptional(key: String, optional: Option[Any], json: Json): Json = {
        optional match {
            case Some(value) => value match {
                case x: Json => Json.obj(key -> x).deepMerge(json)
                case x: Int => Json.obj(key -> x.asJson).deepMerge(json)
                case x: BigInt => Json.obj(key -> x.asJson).deepMerge(json)
                case x: String => Json.obj(key -> x.asJson).deepMerge(json)
                case Value.Struct(a, t) => {
                    val Value.AnonStruct(members) = a
                    val memberJson = members.map((key, value) => (key.toString -> valueAsJson(value))).asJson
                    Json.obj(key -> memberJson).deepMerge(json)
                }
                case x: Value => Json.obj(key -> valueAsJson(x)).deepMerge(json)
                case x: Ast.QueueFull => Json.obj(key -> x.toString.asJson).deepMerge(json)
            }
            case None => json
        }
    }

    /** Returns the updated JSON object with fields of optionalMap added only if they map to Some value*/
    private def jsonWithOptionalValues(json: Json, optionals: Map[String, Option[Any]]): Json = {
        optionals.foldLeft(json) ((acc, inst) => jsonWithOptional(inst._1, inst._2, acc))
    }

    /** Helper function to concatenate annotations List[String] together and return Option[String] for easy encoding */
    private def concatAnnotations(preAnnotation: List[String], postAnnotation: List[String]): Option[String] = {
        val concat = (preAnnotation ++ postAnnotation).mkString("\n")
        if (concat.isEmpty) None else Some(concat)
    }

     /** Given a set of symbols, returns subset consisting of array, enum, and struct symbols */
    private def splitTypeSymbolSet(symbolSet: Set[Symbol], outSet: Set[Symbol]): (Set[Symbol]) = {
        if (symbolSet.isEmpty) (outSet) else {
            val (tail, out) = symbolSet.head match {
                case h: (Symbol.Array | Symbol.Enum | Symbol.Struct) => (symbolSet.tail, outSet + h)
                case _ => (symbolSet.tail, outSet)
            }
            splitTypeSymbolSet(tail, out)
        }
    }

}
